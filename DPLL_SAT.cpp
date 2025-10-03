#include <bits/stdc++.h>
using namespace std;

bool parse_dimacs(istream &in, int &nvars, vector<vector<int>> &clauses) {
    string line;
    nvars = 0;
    while (getline(in, line)) {
        if (line.empty()) continue;
        if (line[0] == 'c') continue;
        if (line[0] == 'p') {
            string tmp; int m;
            stringstream ss(line);
            ss >> tmp >> tmp >> nvars >> m;
            continue;
        }
        stringstream ss(line);
        int x;
        vector<int> clause;
        while (ss >> x) {
            if (x == 0) {
                if (!clause.empty()) clauses.push_back(clause);
                clause.clear();
            } else {
                clause.push_back(x);
                nvars = max(nvars, abs(x));
            }
        }
        if (!clause.empty()) clauses.push_back(clause);
    }
    return true;
}

// assignment: -1 unassigned, 0 false, 1 true
// apply unit propagation; returns false if conflict found
bool unit_propagate(vector<int> &assign, vector<vector<int>> &clauses, vector<int> &trail) {
    bool changed = true;
    while (changed) {
        changed = false;
        for (auto &cl : clauses) {
            int unassigned_count = 0;
            int last_unassigned_lit = 0;
            bool satisfied = false;
            for (int lit : cl) {
                int v = abs(lit);
                int val = assign[v];
                if (val == -1) {
                    unassigned_count++;
                    last_unassigned_lit = lit;
                } else {
                    bool lit_true = (lit > 0) ? (val == 1) : (val == 0);
                    if (lit_true) { satisfied = true; break; }
                }
            }
            if (satisfied) continue;
            if (unassigned_count == 0) {
                // clause unsatisfied -> conflict
                return false;
            }
            if (unassigned_count == 1) {
                // unit clause -> assign last_unassigned_lit
                int v = abs(last_unassigned_lit);
                int want = (last_unassigned_lit > 0) ? 1 : 0;
                if (assign[v] == -1) {
                    assign[v] = want;
                    trail.push_back(last_unassigned_lit);
                    changed = true;
                } else {
                    // already assigned, check consistency
                    if (assign[v] != want) return false;
                }
            }
        }
    }
    return true;
}

bool all_clauses_satisfied(const vector<int> &assign, const vector<vector<int>> &clauses) {
    for (auto &cl : clauses) {
        bool sat = false;
        for (int lit : cl) {
            int v = abs(lit);
            int val = assign[v];
            if (val != -1) {
                bool lit_true = (lit > 0) ? (val == 1) : (val == 0);
                if (lit_true) { sat = true; break; }
            } else {
                sat = false; // unknown, can't conclude clause satisfied
            }
        }
        if (!sat) {
            // clause not (yet) satisfied — could still be satisfied later
            bool possible = false;
            for (int lit : cl) {
                if (assign[abs(lit)] == -1) { possible = true; break; }
            }
            if (!possible) return false; // impossible to satisfy
        }
    }
    return true;
}

int choose_variable(const vector<int> &assign) {
    int n = (int)assign.size() - 1;
    for (int v = 1; v <= n; ++v) if (assign[v] == -1) return v;
    return -1;
}

bool dpll(vector<int> &assign, vector<vector<int>> &clauses) {
    vector<int> trail; // track new assignments for easy backtrack in this stack frame
    if (!unit_propagate(assign, clauses, trail)) {
        // conflict during propagation -> backtrack
        for (int lit : trail) assign[abs(lit)] = -1;
        return false;
    }

    // check if all clauses satisfied
    bool allSat = true;
    for (auto &cl : clauses) {
        bool sat = false;
        for (int lit : cl) {
            int v = abs(lit), val = assign[v];
            if (val != -1) {
                bool lit_true = (lit > 0) ? (val == 1) : (val == 0);
                if (lit_true) { sat = true; break; }
            } else {
                // unknown literal means clause could still be satisfied later
                sat = false;
            }
        }
        if (!sat) {
            // check if clause still has unassigned literal
            bool hasUnassigned = false;
            for (int lit : cl) if (assign[abs(lit)] == -1) { hasUnassigned = true; break; }
            if (!hasUnassigned) { // clause is definitively unsatisfied
                allSat = false;
                break;
            } else {
                allSat = false;
            }
        }
    }
    if (allSat) {
        // complete model found
        return true;
    }

    int var = choose_variable(assign);
    if (var == -1) {
        // no variable to choose but not all clauses satisfied -> unsat
        for (int lit : trail) assign[abs(lit)] = -1;
        return false;
    }

    // try true
    assign[var] = 1;
    if (dpll(assign, clauses)) return true;
    // backtrack assignations done in deeper calls (they restored themselves), but current var still set
    // undo and try false
    assign[var] = 0;
    if (dpll(assign, clauses)) return true;

    // backtrack this variable
    assign[var] = -1;
    for (int lit : trail) assign[abs(lit)] = -1;
    return false;
}

int main(int argc, char **argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    istream *in = &cin;
    ifstream fin;
    if (argc >= 2) {
        fin.open(argv[1]);
        if (fin) in = &fin;
    }

    int nvars;
    vector<vector<int>> clauses;
    parse_dimacs(*in, nvars, clauses);

    vector<int> assign(nvars + 1, -1); // 1-based indexing

    bool sat = dpll(assign, clauses);

    if (!sat) {
        cout << "UNSAT\n";
    } else {
        cout << "SAT\n";
        for (int v = 1; v <= nvars; ++v) {
            int val = assign[v];
            if (val == -1) val = 1; // default to true if unassigned
            cout << (val ? v : -v) << (v == nvars ? '\n' : ' ');
        }
    }
    return 0;
}

