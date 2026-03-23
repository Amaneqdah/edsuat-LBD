# EduSAT + LBD

An enhanced version of the **EduSAT** SAT solver, extended with **LBD-based clause management** and improvements to the **CDCL (Conflict-Driven Clause Learning)** solving process.

This project was developed as part of a SAT solving / Algorithms in Logic course project, with the goal of improving solver performance on benchmark CNF instances.

---

## Overview

This repository contains a modified version of the EduSAT solver with additional heuristics for managing learned clauses more effectively.

The main enhancement in this version is the use of **LBD (Literal Block Distance)** as a quality measure for learned clauses.  
LBD helps estimate how useful a learned clause is, allowing the solver to keep stronger clauses and delete weaker ones during the search.

---

## Main Improvements

- Added **LBD computation** for learned clauses
- Integrated **LBD-based learned clause evaluation**
- Added **dynamic clause deletion heuristics**
- Improved learned clause management during CDCL solving
- Evaluated performance on benchmark CNF inputs

---

## What is LBD?

**LBD (Literal Block Distance)** is a measure of the number of distinct decision levels appearing in a learned clause.

A lower LBD value usually indicates a stronger and more useful clause.  
This makes LBD a practical heuristic for deciding which learned clauses should be kept and which can be deleted.

---

## Project Structure

Typical project files include:

- `edusat.cpp` – main solver implementation
- `edusat.h` – solver declarations and core data structures
- `options.h` – configuration / command-line options
- `assignment.txt` – assignment output for SAT instances
- CNF benchmark files – input formulas in DIMACS CNF format

> File names may vary slightly depending on the final version of the project.

---

## Solver Features

This solver is based on the **CDCL** framework and includes:

- Unit propagation
- Conflict analysis
- Learned clause generation
- Backtracking / backjumping
- Restart policy
- LBD-based clause scoring
- Clause database reduction

---

## Build

Compile the project using a C++ compiler such as `g++`.

Example:

```bash
g++ -O2 -std=c++17 edusat.cpp -o edusat
```

If your project includes additional source files, add them to the compilation command as needed.


## Output

The solver prints the solving process and final result:

- `SAT` – if the formula is satisfiable
- `UNSAT` – if the formula is unsatisfiable

For satisfiable instances, the assignment may also be written to:

- `assignment.txt`

The solver may also print statistics such as:

- Number of restarts
- Number of conflicts
- Number of learned clauses
- Number of decisions
- Number of implications
- Runtime

---

## License

This project is for educational and academic use.
