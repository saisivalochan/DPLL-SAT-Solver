#include <bits/stdc++.h>
using namespace std;

struct Clause {
    vector<int> lits;
    int w1=-1, w2=-1;
};

struct Solver {
    int nvars=0, nclauses=0;
    vector<Clause> clauses;
    vector<vector<int>> watches;
    vector<int> assignv, level, reason, trail, assignLit, polarity;
    int qhead=0, currLevel=0;
    bool unsat=false;

    static inline int var(int lit){ return lit>>1; }
    static inline int sign(int lit){ return lit&1; }
    static inline int neg(int lit){ return lit^1; }

    int value_lit(int lit){
        int v = var(lit);
        int a = assignv[v];
        if(a==-1) return -1;
        return a ^ sign(lit) ? 0 : 1;
    }

    bool enqueue(int lit, int from_clause){
        int v = var(lit);
        int val = (sign(lit)?0:1);
        if(assignv[v]!=-1) return assignv[v]==val;
        assignv[v]=val;
        level[v]=currLevel;
        reason[v]=from_clause;
        assignLit[v]=lit;
        trail.push_back(lit);
        return true;
    }

    int propagate(){
        while(qhead<(int)trail.size()){
            int lit = trail[qhead++];
            int p = neg(lit);
            auto &ws = watches[p];
            int i=0;
            while(i<(int)ws.size()){
                int cid = ws[i];
                Clause &c = clauses[cid];
                int wi = (c.lits[c.w1]==p ? 1 : (c.lits[c.w2]==p ? 2 : 0));
                if(!wi){ i++; continue; }
                int otherIdx = (wi==1? c.w2 : c.w1);
                int other = c.lits[otherIdx];
                bool moved=false;
                for(int k=0;k<(int)c.lits.size();k++){
                    int litk = c.lits[k];
                    if(litk==p || litk==other) continue;
                    if(value_lit(litk)!=0){
                        if(wi==1) c.w1=k; else c.w2=k;
                        watches[litk].push_back(cid);
                        ws[i]=ws.back();
                        ws.pop_back();
                        moved=true;
                        break;
                    }
                }
                if(moved) continue;
                int valOther = value_lit(other);
                if(valOther==1){ i++; continue; }
                if(valOther==-1){
                    if(!enqueue(other, cid)) return cid;
                    i++;
                }else{
                    return cid;
                }
            }
        }
        return -1;
    }

    void backtrack(int lvl){
        while(!trail.empty()){
            int lit = trail.back();
            int v = var(lit);
            if(level[v]<=lvl) break;
            assignv[v]=-1;
            reason[v]=-1;
            assignLit[v]=-1;
            trail.pop_back();
        }
        qhead = (int)trail.size();
        currLevel=lvl;
    }

    void analyze(int confl, vector<int>& out_clause, int& out_btlevel){
        vector<char> seen(nvars,0);
        out_clause.clear();
        int counter=0;
        auto add = [&](const Clause& c){
            for(int q: c.lits){
                int v=var(q);
                if(seen[v]) continue;
                seen[v]=1;
                if(level[v]==currLevel) counter++;
                else out_clause.push_back(q);
            }
        };
        add(clauses[confl]);
        int idx=(int)trail.size()-1;
        int p=-1;
        while(true){
            while(true){
                int lit = trail[idx--];
                if(seen[var(lit)] && level[var(lit)]==currLevel){ p=lit; break; }
            }
            if(--counter==0) break;
            int v = var(p);
            int rc = reason[v];
            if(rc!=-1) add(clauses[rc]);
        }
        out_clause.push_back(neg(p));
        int mbl=0;
        for(int i=0;i<(int)out_clause.size()-1;i++){
            int lv = level[var(out_clause[i])];
            if(lv>mbl) mbl=lv;
        }
        out_btlevel=mbl;
    }

    int pickBranchLit(){
        for(int v=0;v<nvars;v++){
            if(assignv[v]==-1){
                int lit = (polarity[v]? ((v<<1)^1) : (v<<1));
                return lit;
            }
        }
        return -1;
    }

    bool addClause(vector<int> lits){
        if(unsat) return false;
        sort(lits.begin(), lits.end());
        lits.erase(unique(lits.begin(), lits.end()), lits.end());
        for(int x: lits) if(binary_search(lits.begin(), lits.end(), x^1)) return true;
        if(lits.empty()){ unsat=true; return false; }
        Clause c; c.lits=lits;
        if((int)watches.size()==0) watches.assign(2*nvars, {});
        if((int)c.lits.size()==1){
            c.w1=0; c.w2=0;
            clauses.push_back(move(c));
            watches[clauses.back().lits[0]].push_back((int)clauses.size()-1);
            if(!enqueue(clauses.back().lits[0], (int)clauses.size()-1)){ unsat=true; return false; }
        }else{
            c.w1=0; c.w2=1;
            clauses.push_back(move(c));
            int id=(int)clauses.size()-1;
            watches[clauses[id].lits[clauses[id].w1]].push_back(id);
            watches[clauses[id].lits[clauses[id].w2]].push_back(id);
        }
        return true;
    }

    bool solve(){
        if(unsat) return false;
        int confl = propagate();
        if(confl!=-1) return false;
        while(true){
            int decision = pickBranchLit();
            if(decision==-1) return true;
            currLevel++;
            enqueue(decision, -1);
            while(true){
                confl = propagate();
                if(confl==-1) break;
                if(currLevel==0) return false;
                vector<int> learnt;
                int bt=0;
                analyze(confl, learnt, bt);
                backtrack(bt);
                int cid = (int)clauses.size();
                addClause(learnt);
                enqueue(learnt.back(), cid);
            }
        }
    }
};

int main(int argc, char** argv){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    istream* in=&cin;
    if(argc>=2){
        static ifstream f;
        f.open(argv[1]);
        if(f) in=&f;
    }
    string line;
    int nvars=0, nclauses=0;
    vector<vector<int>> rawClauses;
    while(true){
        if(!getline(*in,line)) break;
        if(line.empty()) continue;
        if(line[0]=='c') continue;
        if(line[0]=='p'){
            string tmp;
            stringstream ss(line);
            ss>>tmp>>tmp>>nvars>>nclauses;
            continue;
        }
        stringstream ss(line);
        int x; vector<int> clause;
        while(ss>>x){
            if(x==0){
                if(!clause.empty()) rawClauses.push_back(clause);
                clause.clear();
            }else{
                int v=abs(x)-1;
                int lit = (v<<1) ^ (x<0);
                clause.push_back(lit);
            }
        }
        if(!clause.empty()){
            rawClauses.push_back(clause);
        }
    }
    if(nvars==0){
        for(auto& c: rawClauses) for(int lit: c) nvars=max(nvars, (lit>>1)+1);
    }
    Solver S;
    S.nvars=nvars;
    S.assignv.assign(nvars,-1);
    S.level.assign(nvars,0);
    S.reason.assign(nvars,-1);
    S.assignLit.assign(nvars,-1);
    S.polarity.assign(nvars,0);
    S.watches.assign(2*nvars, {});
    for(auto& c: rawClauses) S.addClause(c);
    bool sat = !S.unsat && S.solve();
    if(!sat){
        cout<<"UNSAT\n";
    }else{
        cout<<"SAT\n";
        for(int i=0;i<S.nvars;i++){
            int val = S.assignv[i];
            if(val==-1) val=1;
            int lit = val? (i+1) : -(i+1);
            cout<<lit<<(i+1==S.nvars?'\n':' ');
        }
    }
    return 0;
}
