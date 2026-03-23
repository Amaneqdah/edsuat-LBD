#pragma once
#include <iostream>
#include <algorithm>
#include <iterator>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <set>
#include <string>
#include <sstream>
#include <fstream>
#include <cassert>
#include <ctime>
#include "options.h"

using namespace std;

typedef int Var;   // Variable
typedef int Lit;   // Literal
typedef vector<Lit> clause_t;
typedef clause_t::iterator clause_it;
typedef vector<Lit> trail_t;

#define Assert(exp) AssertCheck(exp, __func__, __LINE__)

#define Neg(l) (l & 1)
#define Restart_multiplier 1.1f
#define Restart_lower 100
#define Restart_upper 1000
#define Max_bring_forward 10
#define var_decay 0.99
#define Rescale_threshold 1e100
#define Assignment_file "assignment.txt"

int verbose = 0;
double begin_time;
double timeout = 1200;

void Abort(string s, int i);

/*
MINISAT-style variable decision heuristic:
variable activity is increased when variables participate in learned clauses,
and scores are periodically rescaled to preserve numeric stability.
*/
enum class VAR_DEC_HEURISTIC {
	MINISAT
};

VAR_DEC_HEURISTIC VarDecHeuristic = VAR_DEC_HEURISTIC::MINISAT;

/*
Value decision heuristic:
- LITSCORE: choose the literal with higher occurrence count.
- PHASESAVING: reuse the last assigned value of the variable.
*/
enum class VAL_DEC_HEURISTIC {
	PHASESAVING,
	LITSCORE
};

VAL_DEC_HEURISTIC ValDecHeuristic = VAL_DEC_HEURISTIC::PHASESAVING;

/*
Command-line options:
- v: verbosity level
- timeout: solver timeout in seconds
- valdh: value decision heuristic
*/
unordered_map<string, option*> options = {
	{"v",       new intoption(&verbose, 0, 2, "Verbosity level")},
	{"timeout", new doubleoption(&timeout, 0.0, 36000.0, "Timeout in seconds")},
	{"valdh",   new intoption((int*)&ValDecHeuristic, 0, 1, "{0: phase-saving, 1: literal-score}")}
};

/* State of a literal */
enum class LitState {
	L_UNSAT,
	L_SAT,
	L_UNASSIGNED
};

/* State of a variable */
enum class VarState {
	V_FALSE,
	V_TRUE,
	V_UNASSIGNED
};

/* State of a clause */
enum class ClauseState {
	C_UNSAT,
	C_SAT,
	C_UNIT,
	C_UNDEF
};

/* State of the solver */
enum class SolverState {
	UNSAT,
	SAT,
	CONFLICT,
	UNDEF,
	TIMEOUT
};

/***************** service functions **********************/

#ifdef _MSC_VER
#include <ctime>

static inline double cpuTime(void) {
	return (double)clock() / CLOCKS_PER_SEC;
}
#else

#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static inline double cpuTime(void) {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000;
}
#endif

void AssertCheck(bool cond, string func_name, int line, string msg = "") {
	if (cond) return;
	cout << "Assertion fail" << endl;
	cout << msg << endl;
	cout << func_name << " line " << line << endl;
	exit(1);
}

bool match(ifstream& in, char* str) {
	for (; *str != '\0'; ++str) {
		if (*str != in.get()) return false;
	}
	return true;
}

unsigned int Abs(int x) {
	if (x < 0) return (unsigned int)-x;
	return (unsigned int)x;
}

/*
Map an external CNF literal to the solver's internal literal encoding.
Example:
  5  -> 10
 -5  -> 9
*/
unsigned int v2l(int i) {
	if (i < 0) return ((-i) << 1) - 1;
	return i << 1;
}

/* Map an internal literal back to its variable index. */
Var l2v(Lit l) {
	return (l + 1) / 2;
}

/* Return the negation of an internal literal. */
Lit negate(Lit l) {
	if (Neg(l)) return l + 1;
	return l - 1;
}

/* Convert an internal literal to its signed external representation. */
int l2rl(int l) {
	return Neg(l) ? -((l + 1) / 2) : l / 2;
}

/********** classes ******/

class Clause {
	clause_t c;   // literals in internal representation
	int lw, rw;   // indices of the watched literals

public:
	Clause() {};

	void insert(int i) { c.push_back(i); }
	void lw_set(int i) { lw = i; }
	void rw_set(int i) { rw = i; }

	clause_t& cl() { return c; }
	int get_lw() { return lw; }
	int get_rw() { return rw; }
	int get_lw_lit() { return c[lw]; }
	int get_rw_lit() { return c[rw]; }
	int lit(int i) { return c[i]; }

	/*
	If one watched literal becomes false, scan the clause for another
	non-false literal to watch. Otherwise determine whether the clause is:
	- conflicting
	- unit
	- already satisfied
	*/
	inline ClauseState next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc);

	size_t size() { return c.size(); }
	void reset() { c.clear(); }

	void print() {
		for (clause_it it = c.begin(); it != c.end(); ++it) {
			cout << *it << " ";
		}
	}

	void print_real_lits() {
		Lit l;
		cout << "(";
		for (clause_it it = c.begin(); it != c.end(); ++it) {
			l = l2rl(*it);
			cout << l << " ";
		}
		cout << ")";
	}

	void print_with_watches() {
		for (clause_it it = c.begin(); it != c.end(); ++it) {
			cout << l2rl(*it);
			int j = distance(c.begin(), it);
			if (j == lw) cout << "L";
			if (j == rw) cout << "R";
			cout << " ";
		}
	}
};

class Solver {
	vector<Clause> cnf;       // Clause database
	vector<int> unaries;      // Learned or original unit literals
	trail_t trail;            // Assignment trail
	vector<int> separators;   // Trail boundaries by decision level
	vector<int> LitScore;     // Literal occurrence score
	vector<vector<int>> watches; // Literal -> clause indices
	vector<VarState> state;      // Current assignment
	vector<VarState> prev_state; // Saved phase for phase saving
	vector<int> antecedent;      // Variable -> antecedent clause
	vector<bool> marked;         // Used during conflict analysis
	vector<int> dlevel;          // Variable -> decision level
	vector<int> conflicts_at_dl; // Decision level -> learned clauses count snapshot

	// Variable-activity data structures (MINISAT / VSIDS style)
	map<double, unordered_set<Var>, greater<double>> m_Score2Vars;
	map<double, unordered_set<Var>, greater<double>>::iterator m_Score2Vars_it;
	unordered_set<Var>::iterator m_VarsSameScore_it;
	vector<double> m_activity;   // Variable activity
	double m_var_inc;            // Current activity increment
	double m_curr_activity;
	bool m_should_reset_iterators;

	// Learnt-clause management data structures
	map<int, int> clauseLbdByIndex;
	map<int, double> clauseActivityByIndex;
	map<int, double> clauseRetentionScoreByIndex;
	vector<int> lastDeletedClauseIndices;
	map<Var, double> pendingVariableActivityUpdates;

	unsigned int
		nvars,                       // Number of variables
		nclauses,                    // Number of clauses
		nlits,                       // Number of literals = 2 * nvars
		qhead,                       // Propagation head in trail
		totalConflictCount,          // Total number of conflicts
		conflictsSinceLastClauseCleanup,
		clauseCleanupCount;          // Number of learnt-clause cleanup phases

	int
		num_learned,
		num_decisions,
		num_assignments,
		num_restarts,
		dl,                          // Current decision level
		max_dl,                      // Maximum decision level since last restart
		conflicting_clause_idx,      // Current conflicting clause index
		restart_threshold,
		restart_lower,
		restart_upper;

	Lit asserted_lit;              // Asserting literal of the latest learned clause
	float restart_multiplier;

	// access
	int get_learned() { return num_learned; }
	void set_nvars(int x) { nvars = x; }
	int get_nvars() { return nvars; }
	void set_nclauses(int x) { nclauses = x; }
	size_t cnf_size() { return cnf.size(); }
	VarState get_state(int x) { return state[x]; }

	// misc
	void add_to_trail(int x) { trail.push_back(x); }

	void reset();
	void initialize();
	void reset_iterators(double activity_key = 0.0);

	// solving
	SolverState decide();
	void test();
	SolverState BCP();
	int analyze(const Clause);

	// Variable activity update helpers
	void applyVariableActivityUpdate(Var v, double new_score);
	void queueVariableActivityBoost(Var v);
	void applyPendingVariableActivityUpdates();

	// Learnt-clause scoring helpers
	bool isClauseAssertingAtLevel(int clause_index, int conflict_level);
	void refreshClauseLbd(int clause_index);
	int computeClauseLbd(int clause_index);
	double computeClauseActivity(int clause_index);
	double computeClauseRetentionScore(int clause_index);
	void recomputeLearntClauseScores();
	vector<pair<int, double>> rankLearntClausesByScore();

	// Clause deletion and remapping helpers
	void remapClauseIndexInWatches(int clause_index, int recalculated_index);
	void remapClauseIndexInAntecedents(int clause_index, int recalculated_index);
	void remapClauseScoreEntry(int clause_index, int recalculated_index);
	map<int, int> buildClauseIndexRemap(vector<pair<int, double>>& rankedLearntClauses);
	vector<int> collectClausesForDeletionAndFinalizeRemap(map<int, int>& clauseIndexRemap);
	void applyClauseDeletionRemap(map<int, int>& clauseIndexRemap);
	vector<int> eraseClausesFromDatabase(vector<int>& clausesToDelete);
	void backtrackAfterClauseDeletion(int k);
	int computeSafeBacktrackLevelForDeletion(vector<int>& clausesToDelete);
	void clearAntecedent(Var variable);

	inline int getVal(Var v);
	inline void add_clause(Clause& c, int l, int r);
	inline void add_unary_clause(Lit l);
	inline void assert_lit(Lit l);
	void m_rescaleScores(double& new_score);
	inline void backtrack(int k);
	void restart();

	// score updates
	inline void bumpVarScore(int idx);
	inline void bumpLitScore(int lit_idx);

public:
	Solver() :
		nvars(0), nclauses(0), num_learned(0), num_decisions(0), num_assignments(0),
		num_restarts(0), m_var_inc(1.0), qhead(0),
		totalConflictCount(0), conflictsSinceLastClauseCleanup(0), clauseCleanupCount(0),
		restart_threshold(Restart_lower), restart_lower(Restart_lower),
		restart_upper(Restart_upper), restart_multiplier(Restart_multiplier) {
	};

	inline LitState lit_state(Lit l) {
		VarState var_state = state[l2v(l)];
		return var_state == VarState::V_UNASSIGNED
			? LitState::L_UNASSIGNED
			: (Neg(l) && var_state == VarState::V_FALSE || !Neg(l) && var_state == VarState::V_TRUE)
			? LitState::L_SAT
			: LitState::L_UNSAT;
	}

	inline LitState lit_state(Lit l, VarState var_state) {
		return var_state == VarState::V_UNASSIGNED
			? LitState::L_UNASSIGNED
			: (Neg(l) && var_state == VarState::V_FALSE || !Neg(l) && var_state == VarState::V_TRUE)
			? LitState::L_SAT
			: LitState::L_UNSAT;
	}

	void read_cnf(ifstream& in);
	SolverState _solve();
	void solve();

	// debugging
	void print_cnf() {
		for (vector<Clause>::iterator i = cnf.begin(); i != cnf.end(); ++i) {
			i->print_with_watches();
			cout << endl;
		}
	}

	void print_real_cnf() {
		for (vector<Clause>::iterator i = cnf.begin(); i != cnf.end(); ++i) {
			i->print_real_lits();
			cout << endl;
		}
	}

	void print_state(const char* file_name) {
		ofstream out;
		out.open(file_name);
		out << "State: ";
		for (vector<VarState>::iterator it = state.begin() + 1; it != state.end(); ++it) {
			char sign = (*it) == VarState::V_FALSE ? -1 : (*it) == VarState::V_TRUE ? 1 : 0;
			out << sign * (it - state.begin()) << " ";
			out << endl;
		}
	}

	void print_state() {
		cout << "State: ";
		for (vector<VarState>::iterator it = state.begin() + 1; it != state.end(); ++it) {
			char sign = (*it) == VarState::V_FALSE ? -1 : (*it) == VarState::V_TRUE ? 1 : 0;
			cout << sign * (it - state.begin()) << " ";
			cout << endl;
		}
	}

	void print_cnf_state() {
		cout << "CNF State: " << endl;
		for (int i = 0; i < cnf.size(); i++) {
			cout << i << ") ";
			cnf[i].print_real_lits();
			cout << endl;
		}
	}

	void print_antecedents() {
		cout << "Antecedents: " << endl;
		for (int i = 0; i < antecedent.size(); i++) {
			if (antecedent[i] != -1) {
				cout << "ant[" << i << "] = " << antecedent[i] << ";" << endl;
			}
		}
	}

	void print_watches() {
		for (vector<vector<int>>::iterator it = watches.begin() + 1; it != watches.end(); ++it) {
			cout << distance(watches.begin(), it) << ": ";
			for (vector<int>::iterator it_c = (*it).begin(); it_c != (*it).end(); ++it_c) {
				cnf[*it_c].print();
				cout << "; ";
			}
			cout << endl;
		}
	}

	void print_stats() {
		cout << endl << "Statistics: " << endl << "===================" << endl <<
			"### Restarts:\t\t" << num_restarts << endl <<
			"### Dynamic restarts:\t" << clauseCleanupCount << endl <<
			"### Conflicts:\t\t" << totalConflictCount << endl <<
			"### Learned-clauses:\t" << num_learned << endl <<
			"### Decisions:\t\t" << num_decisions << endl <<
			"### Implications:\t" << num_assignments - num_decisions << endl <<
			"### Time:\t\t" << cpuTime() - begin_time << endl;
	}

	void validate_assignment();
};