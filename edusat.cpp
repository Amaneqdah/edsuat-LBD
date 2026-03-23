#include "edusat.h"

int localRestartCount = 0;
Solver S;

using namespace std;

inline bool verbose_now() {
    return false;
}

/****************** Reading the CNF ******************************/
#pragma region readCNF

void skipLine(ifstream& in) {
    for (;;) {
        if (in.get() == '\n') {
            return;
        }
    }
}

static void skipWhitespace(ifstream& in, char& c) {
    c = in.get();
    while ((c >= 9 && c <= 13) || c == 32) {
        c = in.get();
    }
}

static int parseInt(ifstream& in) {
    int val = 0;
    bool neg = false;
    char c;
    skipWhitespace(in, c);
    if (c == '-') {
        neg = true;
        c = in.get();
    }
    if (c < '0' || c > '9') {
        cout << c;
        Abort("Unexpected char in input", 1);
    }
    while (c >= '0' && c <= '9') {
        val = val * 10 + (c - '0');
        c = in.get();
    }
    return neg ? -val : val;
}

void Solver::read_cnf(ifstream& in) {
    int i;
    unsigned int vars, clauses, unary = 0;
    set<Lit> s;
    Clause c;

    while (in.peek() == 'c') {
        skipLine(in);
    }

    if (!match(in, "p cnf")) {
        Abort("Expecting `p cnf' in the beginning of the input file", 1);
    }

    in >> vars;
    in >> clauses;

    if (!vars || !clauses) {
        Abort("Expecting non-zero variables and clauses", 1);
    }

    cout << "vars: " << vars << " clauses: " << clauses << endl;
    cnf.reserve(clauses);

    set_nvars(vars);
    set_nclauses(clauses);
    initialize();

    while (in.good() && in.peek() != EOF) {
        i = parseInt(in);

        if (i == 0) {
            c.cl().resize(s.size());
            copy(s.begin(), s.end(), c.cl().begin());

            switch (c.size()) {
            case 0: {
                stringstream num;
                num << cnf_size() + 1;
                Abort("Empty clause not allowed in input formula (clause " + num.str() + ")", 1);
            }
            case 1: {
                Lit l = c.cl()[0];
                if (state[l2v(l)] != VarState::V_UNASSIGNED) {
                    if (Neg(l) != (state[l2v(l)] == VarState::V_FALSE)) {
                        S.print_stats();
                        Abort("UNSAT (conflicting unaries for var " + to_string(l2v(l)) + ")", 0);
                    }
                }
                assert_lit(l);
                add_unary_clause(l);
                break;
            }
            default:
                add_clause(c, 0, 1);
            }

            c.reset();
            s.clear();
            continue;
        }

        if (Abs(i) > vars) {
            Abort("Literal index larger than declared on the first line", 1);
        }

        if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
            bumpVarScore(abs(i));
        }

        i = v2l(i);

        if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) {
            bumpLitScore(i);
        }

        s.insert(i);
    }

    if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
        reset_iterators();
    }

    cout << "Read " << cnf_size() << " clauses in " << cpuTime() - begin_time
        << " secs." << endl
        << "Solving..." << endl;
}

#pragma endregion readCNF

/****************** Solving ******************************/
#pragma region solving

void Solver::reset() {
    dl = 0;
    max_dl = 0;
    conflicting_clause_idx = -1;
    separators.push_back(0);
    conflicts_at_dl.push_back(0);
}

inline void Solver::reset_iterators(double where) {
    if (verbose_now()) {
        cout << "reset_iterators - where = " << where << endl;
    }

    m_Score2Vars_it = (where == 0) ? m_Score2Vars.begin() : m_Score2Vars.lower_bound(where);
    Assert(m_Score2Vars_it != m_Score2Vars.end());
    m_VarsSameScore_it = m_Score2Vars_it->second.begin();

    if (verbose_now()) {
        cout << "m_Score2Vars_it->first = " << m_Score2Vars_it->first << endl;
    }

    m_should_reset_iterators = false;
}

void Solver::initialize() {
    state.resize(nvars + 1, VarState::V_UNASSIGNED);
    prev_state.resize(nvars + 1, VarState::V_FALSE);
    antecedent.resize(nvars + 1, -1);
    marked.resize(nvars + 1);
    dlevel.resize(nvars + 1);

    nlits = 2 * nvars;
    watches.resize(nlits + 1);
    LitScore.resize(nlits + 1);

    m_activity.resize(nvars + 1);
    m_curr_activity = 0.0f;

    for (unsigned int v = 0; v <= nvars; ++v) {
        m_activity[v] = 0;
    }

    reset();
}

inline void Solver::assert_lit(Lit l) {
    trail.push_back(l);
    int var = l2v(l);

    if (Neg(l)) {
        prev_state[var] = state[var] = VarState::V_FALSE;
    }
    else {
        prev_state[var] = state[var] = VarState::V_TRUE;
    }

    dlevel[var] = dl;
    ++num_assignments;

    if (verbose_now()) {
        cout << l2rl(l) << " @ " << dl << endl;
    }
}

void Solver::m_rescaleScores(double& new_score) {
    if (verbose_now()) {
        cout << "Rescale" << endl;
    }

    new_score /= Rescale_threshold;

    for (unsigned int i = 1; i <= nvars; i++) {
        m_activity[i] /= Rescale_threshold;
    }

    m_var_inc /= Rescale_threshold;

    map<double, unordered_set<Var>, greater<double>> tmp_map;
    double prev_score = 0.0f;

    for (auto m : m_Score2Vars) {
        double scaled_score = m.first / Rescale_threshold;
        if (scaled_score == prev_score) {
            tmp_map[scaled_score].insert(m_Score2Vars[m.first].begin(), m_Score2Vars[m.first].end());
        }
        else {
            tmp_map[scaled_score] = m_Score2Vars[m.first];
        }
        prev_score = scaled_score;
    }

    tmp_map.swap(m_Score2Vars);
}

void Solver::bumpVarScore(int var_idx) {
    double new_score;
    double score = m_activity[var_idx];

    if (score > 0) {
        Assert(m_Score2Vars.find(score) != m_Score2Vars.end());
        m_Score2Vars[score].erase(var_idx);
        if (m_Score2Vars[score].size() == 0) {
            m_Score2Vars.erase(score);
        }
    }

    new_score = score + m_var_inc;
    m_activity[var_idx] = new_score;

    if (new_score > Rescale_threshold) {
        m_rescaleScores(new_score);
    }

    if (m_Score2Vars.find(new_score) != m_Score2Vars.end()) {
        m_Score2Vars[new_score].insert(var_idx);
    }
    else {
        m_Score2Vars[new_score] = unordered_set<int>({ var_idx });
    }
}

void Solver::bumpLitScore(int lit_idx) {
    LitScore[lit_idx]++;
}

void Solver::add_clause(Clause& c, int l, int r) {
    Assert(c.size() > 1);
    c.lw_set(l);
    c.rw_set(r);

    int loc = static_cast<int>(cnf.size());

    watches[c.lit(l)].push_back(loc);
    watches[c.lit(r)].push_back(loc);
    cnf.push_back(c);
}

void Solver::add_unary_clause(Lit l) {
    unaries.push_back(l);
}

int Solver::getVal(Var v) {
    switch (ValDecHeuristic) {
    case VAL_DEC_HEURISTIC::PHASESAVING: {
        VarState saved_phase = prev_state[v];
        switch (saved_phase) {
        case VarState::V_FALSE: return v2l(-v);
        case VarState::V_TRUE:  return v2l(v);
        default: Assert(0);
        }
    }
    case VAL_DEC_HEURISTIC::LITSCORE: {
        int litp = v2l(v), litn = v2l(-v);
        int pScore = LitScore[litp], nScore = LitScore[litn];
        return pScore > nScore ? litp : litn;
    }
    default:
        Assert(0);
    }

    return 0;
}

SolverState Solver::decide() {
    if (verbose_now()) {
        cout << "decide" << endl;
    }

    Lit best_lit = 0;

    switch (VarDecHeuristic) {
    case VAR_DEC_HEURISTIC::MINISAT: {
        if (m_should_reset_iterators) {
            reset_iterators(m_curr_activity);
        }

        Var v = 0;

        if (m_Score2Vars_it == m_Score2Vars.end()) {
            break;
        }

        while (true) {
            while (m_VarsSameScore_it != m_Score2Vars_it->second.end()) {
                v = *m_VarsSameScore_it;
                ++m_VarsSameScore_it;

                if (state[v] == VarState::V_UNASSIGNED) {
                    m_curr_activity = m_Score2Vars_it->first;
                    assert(m_curr_activity == m_activity[v]);
                    best_lit = getVal(v);
                    goto Apply_decision;
                }
            }

            ++m_Score2Vars_it;
            applyPendingVariableActivityUpdates();

            if (m_Score2Vars_it == m_Score2Vars.end()) {
                break;
            }

            m_VarsSameScore_it = m_Score2Vars_it->second.begin();
        }
        break;
    }
    default:
        Assert(0);
    }

    assert(!best_lit);
    S.print_state(Assignment_file);
    return SolverState::SAT;

Apply_decision:
    dl++;

    if (dl > max_dl) {
        max_dl = dl;
        separators.push_back(trail.size());
        conflicts_at_dl.push_back(num_learned);
    }
    else {
        separators[dl] = trail.size();
        conflicts_at_dl[dl] = num_learned;
    }

    assert_lit(best_lit);
    ++num_decisions;
    return SolverState::UNDEF;
}

inline ClauseState Clause::next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc) {
    if (verbose_now()) {
        cout << "next_not_false" << endl;
    }

    if (!binary) {
        for (vector<int>::iterator it = c.begin(); it != c.end(); ++it) {
            LitState litState = S.lit_state(*it);
            if (litState != LitState::L_UNSAT && *it != other_watch) {
                loc = distance(c.begin(), it);
                if (is_left_watch) {
                    lw = loc;
                }
                else {
                    rw = loc;
                }
                return ClauseState::C_UNDEF;
            }
        }
    }

    switch (S.lit_state(other_watch)) {
    case LitState::L_UNSAT:
        if (verbose_now()) {
            print_real_lits();
            cout << " is conflicting" << endl;
        }
        return ClauseState::C_UNSAT;
    case LitState::L_UNASSIGNED:
        return ClauseState::C_UNIT;
    case LitState::L_SAT:
        return ClauseState::C_SAT;
    default:
        Assert(0);
        return ClauseState::C_UNDEF;
    }
}

void Solver::test() {
    for (unsigned int idx = 0; idx < cnf.size(); ++idx) {
        Clause c = cnf[idx];
        bool found = false;

        for (int zo = 0; zo <= 1; ++zo) {
            for (vector<int>::iterator it = watches[c.cl()[zo]].begin(); !found && it != watches[c.cl()[zo]].end(); ++it) {
                if (*it == idx) {
                    found = true;
                    break;
                }
            }
        }

        if (!found) {
            cout << "idx = " << idx << endl;
            c.print();
            cout << endl;
            cout << c.size();
        }

        Assert(found);
    }
}

/*
Periodic learnt-clause cleanup is triggered after enough conflicts accumulate.
Before deleting clauses, the solver remaps clause indices and updates all
dependent structures, including watches, antecedents, and score tables.
*/
SolverState Solver::BCP() {
    if (verbose_now()) {
        cout << "BCP" << endl;
        cout << "qhead = " << qhead << " trail-size = " << trail.size() << endl;
    }

    while (qhead < trail.size()) {
        Lit negatedLit = negate(trail[qhead++]);
        Assert(lit_state(negatedLit) == LitState::L_UNSAT);

        if (verbose_now()) {
            cout << "propagating " << l2rl(negate(negatedLit)) << endl;
        }

        vector<int> new_watch_list;
        int new_watch_list_idx = watches[negatedLit].size() - 1;
        new_watch_list.resize(watches[negatedLit].size());

        for (vector<int>::reverse_iterator it = watches[negatedLit].rbegin();
            it != watches[negatedLit].rend() && conflicting_clause_idx < 0; ++it) {

            Clause& c = cnf[*it];
            Lit l_watch = c.get_lw_lit();
            Lit r_watch = c.get_rw_lit();
            bool binary = c.size() == 2;
            bool is_left_watch = (l_watch == negatedLit);
            Lit other_watch = is_left_watch ? r_watch : l_watch;
            int newWatchLocation;

            ClauseState res = c.next_not_false(is_left_watch, other_watch, binary, newWatchLocation);

            if (res != ClauseState::C_UNDEF) {
                new_watch_list[new_watch_list_idx--] = *it;
            }

            switch (res) {
            case ClauseState::C_UNSAT: {
                if (verbose_now()) {
                    print_state();
                }

                if (dl == 0) {
                    return SolverState::UNSAT;
                }

                conflicting_clause_idx = *it;

                int dist = distance(it, watches[negatedLit].rend()) - 1;
                for (int i = dist - 1; i >= 0; i--) {
                    new_watch_list[new_watch_list_idx--] = watches[negatedLit][i];
                }

                if (verbose_now()) {
                    cout << "conflict" << endl;
                }
                break;
            }

            case ClauseState::C_SAT:
                if (verbose_now()) {
                    cout << "clause is sat" << endl;
                }
                break;

            case ClauseState::C_UNIT: {
                if (verbose_now()) {
                    cout << "propagating: " << endl;
                }

                assert_lit(other_watch);
                antecedent[l2v(other_watch)] = *it;

                if (verbose_now()) {
                    cout << "antecedent[" << l2v(other_watch) << "] = " << *it << endl;
                    cout << "other_watch literal is " << l2rl(other_watch) << endl;
                    cout << "new implication <- " << l2rl(other_watch) << endl;
                }

                // Refresh the LBD of learnt clauses that actively participate in propagation.
                refreshClauseLbd(*it);

                // Reward variables propagated by short, high-impact clauses.
                if (c.size() == 2) {
                    if (verbose_now()) {
                        cout << "activity score += 5 for variable " << l2v(other_watch) << endl;
                    }
                    queueVariableActivityBoost(l2v(other_watch));
                }

                break;
            }

            default: {
                Assert(newWatchLocation < static_cast<int>(c.size()));
                int new_lit = c.lit(newWatchLocation);
                watches[new_lit].push_back(*it);

                if (verbose_now()) {
                    c.print_real_lits();
                    cout << " now watched by " << l2rl(new_lit) << endl;
                }
            }
            }
        }

        watches[negatedLit].clear();
        new_watch_list_idx++;
        watches[negatedLit].insert(
            watches[negatedLit].begin(),
            new_watch_list.begin() + new_watch_list_idx,
            new_watch_list.end()
        );

        if (conflicting_clause_idx >= 0) {
            totalConflictCount++;
            conflictsSinceLastClauseCleanup++;
            return SolverState::CONFLICT;
        }

        new_watch_list.clear();
    }

    return SolverState::UNDEF;
}

int Solver::analyze(const Clause conflicting) {
    if (verbose_now()) {
        cout << "analyze" << endl;
    }

    Clause current_clause = conflicting, new_clause;

    if (verbose_now()) {
        print_antecedents();
    }

    int resolve_num = 0;
    int bktrk = 0;
    int watch_lit = 0;

    Lit u;
    Var v;
    trail_t::reverse_iterator t_it = trail.rbegin();

    do {
        for (clause_it it = current_clause.cl().begin(); it != current_clause.cl().end(); ++it) {
            Lit lit = *it;
            v = l2v(lit);

            if (!marked[v]) {
                marked[v] = true;

                if (dlevel[v] == dl) {
                    ++resolve_num;
                }
                else {
                    new_clause.insert(lit);

                    if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
                        bumpVarScore(v);
                    }

                    if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) {
                        bumpLitScore(lit);
                    }

                    int c_dl = dlevel[v];
                    if (c_dl > bktrk) {
                        bktrk = c_dl;
                        watch_lit = new_clause.size() - 1;
                    }
                }
            }
        }

        while (t_it != trail.rend()) {
            u = *t_it;
            v = l2v(u);
            ++t_it;
            if (marked[v]) {
                break;
            }
        }

        marked[v] = false;
        --resolve_num;

        if (!resolve_num) {
            continue;
        }

        int ant = antecedent[v];

        if (verbose_now()) {
            cout << "u = " << l2rl(u) << endl;
            cout << "v = " << v << endl;
            cout << "antecedent num = " << ant << endl;
        }

        current_clause = cnf[ant];

        if (verbose_now()) {
            cout << "clause " << ant << " = ";
            current_clause.print_real_lits();
            cout << endl;
            cout << "clause cleanup count = " << clauseCleanupCount << endl;
            cout << "last deleted indices: {";
            for (auto itr = lastDeletedClauseIndices.begin(); itr != lastDeletedClauseIndices.end(); itr++) {
                cout << *itr << ";";
            }
            cout << "}" << endl;
            cout << "cnf state right before exception" << endl;
        }

        current_clause.cl().erase(find(current_clause.cl().begin(), current_clause.cl().end(), u));

    } while (resolve_num > 0);

    for (clause_it it = new_clause.cl().begin(); it != new_clause.cl().end(); ++it) {
        marked[l2v(*it)] = false;
    }

    Lit negated_u = negate(u);
    new_clause.cl().push_back(negated_u);

    if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
        m_var_inc *= 1 / var_decay;
    }

    ++num_learned;
    asserted_lit = negated_u;

    if (new_clause.size() == 1) {
        add_unary_clause(negated_u);
    }
    else {
        add_clause(new_clause, watch_lit, new_clause.size() - 1);
    }

    int idx = cnf.size() - 1;
    int lbd_score = computeClauseLbd(idx);
    clauseLbdByIndex.insert(pair<int, int>(idx, lbd_score));

    double activity_score = computeClauseActivity(idx);
    clauseActivityByIndex.insert(pair<int, double>(idx, activity_score));

    double score = computeClauseRetentionScore(idx);
    clauseRetentionScoreByIndex.insert(pair<int, double>(idx, score));

    if (verbose_now()) {
        cout << "Learned clause #" << cnf_size() + unaries.size() << ". ";
        new_clause.print_real_lits();
        cout << endl;
        cout << " learnt clauses:  " << num_learned;
        cout << " Backtracking to level " << bktrk << endl;
    }

    if (verbose >= 1 && !(num_learned % 1000)) {
        cout << "Learned: " << num_learned << " clauses" << endl;
    }

    return bktrk;
}

void Solver::applyPendingVariableActivityUpdates() {
    if (pendingVariableActivityUpdates.empty()) {
        return;
    }

    for (auto& it : pendingVariableActivityUpdates) {
        Var v = it.first;
        double score = it.second;
        applyVariableActivityUpdate(v, score);
    }

    pendingVariableActivityUpdates.clear();
}

void Solver::queueVariableActivityBoost(Var v) {
    double score;

    if (pendingVariableActivityUpdates.find(v) == pendingVariableActivityUpdates.end()) {
        score = m_activity[v] + 5;
        pendingVariableActivityUpdates.insert(pair<Var, double>(v, score));
    }
    else {
        pendingVariableActivityUpdates[v] += 5;
    }
}

void Solver::applyVariableActivityUpdate(Var v, double new_score) {
    if (verbose_now()) {
        cout << "applyVariableActivityUpdate() Var v = " << v << endl;
    }

    double old_score = m_activity[v];

    m_Score2Vars[m_activity[v]].erase(v);
    m_activity[v] = new_score;

    if (m_Score2Vars.find(m_activity[v]) != m_Score2Vars.end()) {
        m_Score2Vars[m_activity[v]].insert(v);
    }
    else {
        m_Score2Vars[m_activity[v]] = unordered_set<int>({ v });
    }

    if (m_Score2Vars[old_score].size() == 0) {
        if (m_Score2Vars_it->first == old_score) {
            ++m_Score2Vars_it;
        }
        m_Score2Vars.erase(old_score);
    }
}

bool Solver::isClauseAssertingAtLevel(int clause_index, int conflict_level) {
    int counter_conflict_levels = 0;
    clause_t clause = cnf[clause_index].cl();

    for (clause_it it = clause.begin(); it != clause.end(); ++it) {
        Var v = l2v(*it);
        if (dlevel[v] == conflict_level) {
            counter_conflict_levels++;
            if (counter_conflict_levels > 1) {
                break;
            }
        }
    }

    return (counter_conflict_levels == 1);
}

void Solver::refreshClauseLbd(int clause_index) {
    if (verbose_now()) {
        cout << "refreshClauseLbd() clause id = " << clause_index << endl;
    }

    if (clauseLbdByIndex.find(clause_index) != clauseLbdByIndex.end()) {
        int new_lbd_score = computeClauseLbd(clause_index);
        clauseLbdByIndex[clause_index] = new_lbd_score;
    }
}

int Solver::computeClauseLbd(int clause_index) {
    set<Lit> distinct_levels;
    clause_t clause = cnf[clause_index].cl();

    for (clause_it it = clause.begin(); it != clause.end(); ++it) {
        Var v = l2v(*it);
        distinct_levels.insert(dlevel[v]);
    }

    return distinct_levels.size();
}

double Solver::computeClauseActivity(int clause_index) {
    double activity = 0.0;
    clause_t clause = cnf[clause_index].cl();

    for (clause_it it = clause.begin(); it != clause.end(); ++it) {
        Var v = l2v(*it);
        activity += m_activity[v];
    }

    return activity;
}

double Solver::computeClauseRetentionScore(int clause_index) {
    double score = 0.0;
    int lbd_score = clauseLbdByIndex[clause_index];
    double activity_score = clauseActivityByIndex[clause_index];
    score = 0.7 * lbd_score + 0.3 / activity_score;
    return score;
}

static bool compareClauseScoresAscending(pair<int, double>& a, pair<int, double>& b) {
    return a.second < b.second;
}

void Solver::recomputeLearntClauseScores() {
    for (int clause_idx = 0; clause_idx < cnf.size(); clause_idx++) {
        if (clauseRetentionScoreByIndex.find(clause_idx) != clauseRetentionScoreByIndex.end()) {
            double new_score = computeClauseRetentionScore(clause_idx);
            clauseRetentionScoreByIndex[clause_idx] = new_score;
        }
    }
}

vector<pair<int, double>> Solver::rankLearntClausesByScore() {
    if (verbose_now()) {
        cout << "rankLearntClausesByScore()" << endl;
    }

    vector<pair<int, double>> sorted_vec;

    for (map<int, double>::iterator it = clauseRetentionScoreByIndex.begin();
        it != clauseRetentionScoreByIndex.end(); ++it) {
        sorted_vec.push_back(make_pair(it->first, it->second));
    }

    sort(sorted_vec.begin(), sorted_vec.end(), compareClauseScoresAscending);
    return sorted_vec;
}

int Solver::computeSafeBacktrackLevelForDeletion(vector<int>& clausesToDelete) {
    if (verbose_now()) {
        cout << "computeSafeBacktrackLevelForDeletion()" << endl;
    }

    int size = clausesToDelete.size();
    int min_level = dl - 1;

    for (int i = 0; i < size; i++) {
        int clause_idx = clausesToDelete[i];
        auto it = find(antecedent.begin(), antecedent.end(), clause_idx);
        if (it != antecedent.end()) {
            Var var = it - antecedent.begin();
            min_level = min(min_level, dlevel[var] - 1);
        }
    }

    return max(min_level, 0);
}

void Solver::remapClauseScoreEntry(int clause_index, int recalculated_index) {
    if (verbose_now()) {
        cout << "remapClauseScoreEntry() clause_index = " << clause_index
            << " recalculated_index = " << recalculated_index << endl;
    }

    if (clause_index == recalculated_index) {
        return;
    }

    if (recalculated_index == -1) {
        clauseRetentionScoreByIndex.erase(clause_index);
    }
    else {
        if (clauseRetentionScoreByIndex.find(clause_index) != clauseRetentionScoreByIndex.end()) {
            double score = clauseRetentionScoreByIndex[clause_index];
            clauseRetentionScoreByIndex.erase(clause_index);
            clauseRetentionScoreByIndex.insert(pair<int, double>(recalculated_index, score));
        }
    }
}

void Solver::remapClauseIndexInWatches(int clause_index, int recalculated_index) {
    if (verbose_now()) {
        cout << "remapClauseIndexInWatches() clause_index = " << clause_index
            << " recalculated_index = " << recalculated_index << endl;
    }

    if (clause_index == recalculated_index) {
        return;
    }

    for (int i = 0; i < watches.size(); i++) {
        if (find(watches[i].begin(), watches[i].end(), clause_index) != watches[i].end()) {
            watches[i].erase(remove(watches[i].begin(), watches[i].end(), clause_index), watches[i].end());
            if (recalculated_index != -1) {
                watches[i].push_back(recalculated_index);
            }
        }
    }
}

void Solver::remapClauseIndexInAntecedents(int clause_index, int recalculated_index) {
    if (verbose_now()) {
        cout << "remapClauseIndexInAntecedents() clause_index = " << clause_index
            << " recalculated_index = " << recalculated_index << endl;
    }

    if (clause_index == recalculated_index) {
        return;
    }

    auto it = std::find(antecedent.begin(), antecedent.end(), clause_index);
    if (it != antecedent.end()) {
        std::replace(antecedent.begin(), antecedent.end(), clause_index, recalculated_index);
    }
}

map<int, int> Solver::buildClauseIndexRemap(vector<pair<int, double>>& rankedLearntClauses) {
    if (verbose_now()) {
        cout << "buildClauseIndexRemap()" << endl;
    }

    int learntClauseCount = rankedLearntClauses.size();
    int amount_to_delete = learntClauseCount / 2;
    int removedCount = 0;
    map<int, int> clauseIndexRemap;

    for (int i = learntClauseCount - 1; i >= 0; i--) {
        int clause_index = rankedLearntClauses[i].first;

        if (!isClauseAssertingAtLevel(clause_index, dl) && removedCount < amount_to_delete) {
            removedCount++;
            clauseIndexRemap.insert(pair<int, int>(clause_index, -1));
        }
        else {
            clauseIndexRemap.insert(pair<int, int>(clause_index, clause_index));
        }
    }

    return clauseIndexRemap;
}

vector<int> Solver::collectClausesForDeletionAndFinalizeRemap(map<int, int>& clauseIndexRemap) {
    int deletedSoFar = 0;
    vector<int> clausesToDelete;

    for (int i = 0; i < cnf.size(); i++) {
        if (clauseIndexRemap.find(i) != clauseIndexRemap.end()) {
            if (clauseIndexRemap[i] == -1) {
                deletedSoFar++;
                clausesToDelete.push_back(i);
            }
            else {
                clauseIndexRemap[i] = i - deletedSoFar;
            }
        }
        else {
            clauseIndexRemap[i] = i - deletedSoFar;
        }
    }

    return clausesToDelete;
}

void Solver::applyClauseDeletionRemap(map<int, int>& clauseIndexRemap) {
    if (verbose_now()) {
        cout << "applyClauseDeletionRemap()" << endl;
    }

    for (int clause_index = 0; clause_index < cnf.size(); clause_index++) {
        int recalculated_index = clauseIndexRemap[clause_index];

        if (recalculated_index == -1) {
            clauseLbdByIndex.erase(clause_index);
            clauseActivityByIndex.erase(clause_index);
        }

        remapClauseScoreEntry(clause_index, recalculated_index);
        remapClauseIndexInWatches(clause_index, recalculated_index);
        remapClauseIndexInAntecedents(clause_index, recalculated_index);
    }
}

vector<int> Solver::eraseClausesFromDatabase(vector<int>& clausesToDelete) {
    sort(clausesToDelete.begin(), clausesToDelete.end());

    for (int i = 0; i < clausesToDelete.size(); i++) {
        if (verbose_now()) {
            cout << "erasing from cnf of size = " << cnf.size() << endl
                << "clausesToDelete[" << i << "] = " << clausesToDelete[i]
                << " clausesToDelete[" << i << "]-" << i << " = "
                << clausesToDelete[i] - i << endl;
        }

        cnf.erase(cnf.begin() + (clausesToDelete[i] - i));
    }

    return clausesToDelete;
}

void Solver::backtrackAfterClauseDeletion(int k) {
    if (verbose_now()) {
        cout << "backtrackAfterClauseDeletion()" << endl;
    }

    for (trail_t::iterator it = trail.begin() + separators[k + 1]; it != trail.end(); ++it) {
        Var v = l2v(*it);
        if (dlevel[v]) {
            state[v] = VarState::V_UNASSIGNED;
            clearAntecedent(v);
            if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
                m_curr_activity = max(m_curr_activity, m_activity[v]);
            }
        }
    }

    if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
        m_should_reset_iterators = true;
    }

    trail.erase(trail.begin() + separators[k + 1], trail.end());
    qhead = trail.size();
    dl = k;
    conflicting_clause_idx = -1;
}

void Solver::backtrack(int k) {
    if (verbose_now()) {
        cout << "backtrack" << endl;
    }

    if (k > 0 && (num_learned - conflicts_at_dl[k] > restart_threshold)) {
        localRestartCount++;
        restart();
        return;
    }

    for (trail_t::iterator it = trail.begin() + separators[k + 1]; it != trail.end(); ++it) {
        Var v = l2v(*it);
        if (dlevel[v]) {
            state[v] = VarState::V_UNASSIGNED;
            clearAntecedent(v);
            if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
                m_curr_activity = max(m_curr_activity, m_activity[v]);
            }
        }
    }

    if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
        m_should_reset_iterators = true;
    }

    if (verbose_now()) {
        print_state();
    }

    trail.erase(trail.begin() + separators[k + 1], trail.end());
    qhead = trail.size();
    dl = k;

    assert_lit(asserted_lit);
    antecedent[l2v(asserted_lit)] = cnf.size() - 1;
    conflicting_clause_idx = -1;
}

void Solver::validate_assignment() {
    if (verbose_now()) {
        cout << "validate_assignment()" << endl;
    }

    for (unsigned int i = 1; i <= nvars; ++i) {
        if (state[i] == VarState::V_UNASSIGNED) {
            cout << "Unassigned var: " + to_string(i) << endl;
        }
    }

    for (vector<Clause>::iterator it = cnf.begin(); it != cnf.end(); ++it) {
        int found = 0;

        for (clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c) {
            if (lit_state(*it_c) == LitState::L_SAT) {
                found = 1;
            }
        }

        if (!found) {
            cout << "fail on clause: ";
            it->print();
            cout << endl;

            for (clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c) {
                cout << *it_c << " (" << (int)lit_state(*it_c) << ") ";
            }
            cout << endl;

            Abort("Assignment validation failed", 3);
        }
    }

    for (vector<Lit>::iterator it = unaries.begin(); it != unaries.end(); ++it) {
        if (lit_state(*it) != LitState::L_SAT) {
            Abort("Assignment validation failed (unaries)", 3);
        }
    }

    cout << "Assignment validated" << endl;
}

void Solver::restart() {
    if (verbose_now()) {
        cout << "restart" << endl;
    }

    restart_threshold = static_cast<int>(restart_threshold * restart_multiplier);

    if (restart_threshold > restart_upper) {
        restart_threshold = restart_lower;
        restart_upper = static_cast<int>(restart_upper * restart_multiplier);

        if (verbose >= 1) {
            cout << "new restart upper bound = " << restart_upper << endl;
        }
    }

    if (verbose >= 1) {
        cout << "restart: new threshold = " << restart_threshold << endl;
    }

    ++num_restarts;

    for (unsigned int i = 1; i <= nvars; ++i) {
        if (dlevel[i] > 0) {
            state[i] = VarState::V_UNASSIGNED;
            dlevel[i] = 0;
        }
    }

    trail.clear();
    qhead = 0;
    separators.clear();
    conflicts_at_dl.clear();

    if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
        m_curr_activity = 0;
        m_should_reset_iterators = true;
    }

    reset();
}

void Solver::solve() {
    SolverState res = _solve();
    Assert(res == SolverState::SAT || res == SolverState::UNSAT || res == SolverState::TIMEOUT);

    S.print_stats();

    switch (res) {
    case SolverState::SAT: {
        S.validate_assignment();
        string str = "solution in ", str1 = Assignment_file;
        cout << str + str1 << endl;
        cout << "SAT" << endl;
        break;
    }
    case SolverState::UNSAT:
        cout << "UNSAT" << endl;
        break;
    case SolverState::TIMEOUT:
        cout << "TIMEOUT" << endl;
        return;
    }

    return;
}

SolverState Solver::_solve() {
    SolverState res;

    while (true) {
        if (timeout > 0 && cpuTime() - begin_time > timeout) {
            return SolverState::TIMEOUT;
        }

        while (true) {
            /* Periodic learnt-clause cleanup */
            if (conflictsSinceLastClauseCleanup > 20000 + 500 * clauseCleanupCount &&
                pendingVariableActivityUpdates.empty()) {

                if (verbose_now()) {
                    cout << "dynamic restart" << endl;
                    cout << "antecedents and cnf state before dynamic restart" << endl;
                    print_antecedents();
                }

                recomputeLearntClauseScores();

                vector<pair<int, double>> rankedLearntClauses = rankLearntClausesByScore();
                map<int, int> clauseIndexRemap = buildClauseIndexRemap(rankedLearntClauses);
                vector<int> clausesToDelete = collectClausesForDeletionAndFinalizeRemap(clauseIndexRemap);

                lastDeletedClauseIndices.clear();
                lastDeletedClauseIndices = clausesToDelete;

                int deletionBacktrackLevel = computeSafeBacktrackLevelForDeletion(clausesToDelete);

                applyClauseDeletionRemap(clauseIndexRemap);
                eraseClausesFromDatabase(clausesToDelete);

                clauseCleanupCount++;

                if (verbose_now()) {
                    cout << "dynamic backtracking to level: " << deletionBacktrackLevel << endl;
                    cout << "antecedents state before dynamic restart" << endl;
                    print_antecedents();
                }

                backtrackAfterClauseDeletion(deletionBacktrackLevel);
                conflictsSinceLastClauseCleanup = 0;

                if (verbose_now()) {
                    cout << "dynamic restart over" << endl;
                    cout << "antecedents and cnf state after dynamic restart" << endl;
                    print_antecedents();
                }
            }

            res = BCP();

            if (verbose_now()) {
                cout << "antecedents after BCP" << endl;
                print_antecedents();
                cout << "BCP is over" << endl;
            }

            if (res == SolverState::UNSAT) {
                return res;
            }

            if (res == SolverState::CONFLICT) {
                backtrack(analyze(cnf[conflicting_clause_idx]));
                if (verbose_now()) {
                    cout << "antecedents after backtrack" << endl;
                    print_antecedents();
                }
            }
            else {
                break;
            }
        }

        res = decide();
        if (res == SolverState::SAT) {
            return res;
        }
    }
}

void Solver::clearAntecedent(Var variable) {
    antecedent[variable] = -1;
}

#pragma endregion solving

/****************** main ******************************/
int main(int argc, char** argv) {
    begin_time = cpuTime();
    parse_options(argc, argv);

    ifstream in(argv[argc - 1]);
    if (!in.good()) {
        Abort("cannot read input file", 1);
    }

    cout << "This is edusat" << endl;
    S.read_cnf(in);
    in.close();
    S.solve();

    return 0;
}