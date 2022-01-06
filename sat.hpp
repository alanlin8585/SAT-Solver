#include <set>
#include <vector>
#include <numeric>
#include <fstream>
#include <algorithm>
#include <queue>
#include "parser.h"
using namespace std;

struct sat {
    int restart_rate = 100;
    int maxVarIndex, set_of_literal_cnt, ori_clauses_size, init_clauses_size;
    vector<vector<int>> clauses;
    vector<int> unit_clauses;
    vector<int8_t> var_assigned, var_table;
    ofstream out;
    void output() {
        out << "v ";
        for(int i = 1; i <= maxVarIndex; i++) {
            if(var_table[i]) out << i;
            else out << -i;
            out << " ";
        }
        out << "0\n";
    }
    bool check_sat() {
        bool flag = 1;
        for(vector<int> &i : clauses) {
            flag = 0;
            for(int j : i) {
                if(j > 0 && var_assigned[j] && var_table[j]) {
                    flag = 1;
                    break;
                } else if(j < 0 && var_assigned[-j] && !var_table[-j]) {
                    flag = 1;
                }
            }
            if(!flag) return false;
        }
        return true;
    }

    int abs(int x) {
        return x > 0 ? x : -x;
    }
    void swap(int &a, int &b) {
        int tmp = a;
        a = b, b = tmp;
    }
    // conflict backtracking and learning
    #define learn_rate 100
    int learn_size_limit = 100, not_learned = 0;
    int return_to_level, conflict_clause_id, learn_cnt = 0;
    int try_other_var = 0;
    vector<int> var_assigned_level, var_imply_by_clause, var_assigned_order;
    vector<int8_t> conflict_var_inqueue;
    void conflict_learning(int level) {
        vector<int> inqueue_v;
        set<pair<int, int>, greater<pair<int, int>>> conflict_level;
        vector<int> non_conflict_level;
        return_to_level = 1;
        for(int i : clauses[conflict_clause_id]) {
            if(!conflict_var_inqueue[abs(i)]) {
                conflict_var_inqueue[abs(i)] = 1;
                inqueue_v.push_back(abs(i));
                if(var_assigned_level[abs(i)] == level)
                    conflict_level.insert(make_pair(var_assigned_order[abs(i)], i));
                else
                    non_conflict_level.push_back(i);
            }
        }
        while(conflict_level.size() > 1) {
            int clause_id = var_imply_by_clause[abs(conflict_level.begin() -> second)];
            conflict_level.erase(conflict_level.begin());
            for(int i : clauses[clause_id]) {
                if(!conflict_var_inqueue[abs(i)]) {
                    conflict_var_inqueue[abs(i)] = 1;
                    inqueue_v.push_back(abs(i));
                    if(var_assigned_level[abs(i)] == level)
                        conflict_level.insert(make_pair(var_assigned_order[abs(i)], i));
                    else
                        non_conflict_level.push_back(i);
                }
            }
        }

        if(true) {
            if(!non_conflict_level.empty()) {
                for(int &i : non_conflict_level) 
                    if(return_to_level < var_assigned_level[abs(i)] + 1) {
                        return_to_level = var_assigned_level[abs(i)] + 1;
                        swap(i, non_conflict_level[0]);
                    }
            }
            not_learned = min(0, not_learned - 1); // tag
            if(-not_learned > learn_rate) {
                not_learned = 0;
                learn_size_limit = max(0, learn_size_limit - 1);
            }
            non_conflict_level.push_back(conflict_level.begin() -> second);
        
            int new_clause_id = clauses.size();

            // for two literal
            if(non_conflict_level.size() > 1) {
                swap(non_conflict_level[1], non_conflict_level.back());
                swap(non_conflict_level[0], non_conflict_level[1]);
            }

            clauses.push_back(non_conflict_level);
            watchs.push_back(make_pair(0, 0));
            add_clause(new_clause_id);
            if(unit_clauses.empty())
                unit_clauses.push_back(new_clause_id);
            ++learn_cnt;
        } else {
            return_to_level = level;
            not_learned = max(0, not_learned + 1);
            if(not_learned > learn_rate) {
                not_learned = 0;
                learn_size_limit++;
            }
        }
        conflict_clause_id = -1;
        for(int j : inqueue_v)
            conflict_var_inqueue[j] = 0;
        if(learn_cnt == restart_rate) {
            //learn_cnt = 0;
            return_to_level = 0;
            restart_tag = 1;
        }
    }
    void reduce_learned_clause() {
        size_t stay_size_limit = 10000;
        for(size_t i = ori_clauses_size; i < clauses.size(); i++)
        	stay_size_limit = min(stay_size_limit, clauses[i].size());
        stay_size_limit = max(stay_size_limit, static_cast<size_t>(15));
        size_t top = ori_clauses_size - 1;//stay_size;
        for(size_t i = ori_clauses_size; i < clauses.size(); i++)
            if(clauses[i].size() <= stay_size_limit && ++top != i)
                clauses[top].swap(clauses[i]);
        clauses.resize(top + 1);
    }

    // 2-literal watching
    vector<pair<int, int>> watchs;
    vector<vector<vector<int>>> var_to_watch;
    void add_clause(int clause_id) {
        if(clauses[clause_id].size() <= 10) {
            for(int i : clauses[clause_id]) {
                if(!var_assigned[abs(i)])
                    ranking.erase(make_pair(literal_cnt[abs(i)], abs(i)));
                if(i > 0)
                    posc[i]++;
                else
                    negc[-i]++;
                literal_cnt[abs(i)]++;
                if(!var_assigned[abs(i)])
                    ranking.insert(make_pair(literal_cnt[abs(i)], abs(i)));
            }
        }
        if(clauses[clause_id].empty()) // empty clause
            return;
        if((int)clauses[clause_id].size() == 1) { // unit literal clause
            unit_clauses.push_back(clause_id);
            var_to_watch[clauses[clause_id][0] > 0][abs(clauses[clause_id][0])].push_back(clause_id);
        } else { // mutiple literals clause
            watchs[clause_id] = make_pair(0, 1);
            var_to_watch[clauses[clause_id][0] > 0][abs(clauses[clause_id][0])].push_back(clause_id);
            var_to_watch[clauses[clause_id][1] > 0][abs(clauses[clause_id][1])].push_back(clause_id);
        }
    }
    bool check_all_sat() {
        static int last = 0;
        for(int i = last; i < (int)clauses.size(); i++) {
            int x = clauses[i][watchs[i].first];
            if(var_assigned[abs(x)] && (var_table[abs(x)] ^ (x < 0)))
                continue;
            if(clauses[i].size() == 1) {
                last = i;
                return false;
            }
            x = clauses[i][watchs[i].second];
            if(var_assigned[abs(x)] && (var_table[abs(x)] ^ (x < 0)))
                continue;
            last = i;
            return false;
        }
        for(int i = 0; i < last; i++) {
            int x = clauses[i][watchs[i].first];
            if(var_assigned[abs(x)] && (var_table[abs(x)] ^ (x < 0)))
                continue;
            if(clauses[i].size() == 1) {
                last = i;
                return false;
            }
            x = clauses[i][watchs[i].second];
            if(var_assigned[abs(x)] && (var_table[abs(x)] ^ (x < 0)))
                continue;
            last = i;
            return false;
        }
        return true;
    }
    void two_literals_init() {
        watchs.clear();
        watchs.resize(clauses.size());
        var_to_watch.clear();
        var_to_watch.resize(2, vector<vector<int>>(maxVarIndex + 1));
        for(int i = 0; i < (int)clauses.size(); i++)
            add_clause(i);
    }
    bool set_of_clauses(int clause_id) {
        int x = clauses[clause_id][watchs[clause_id].first];
        if(var_assigned[abs(x)] && (var_table[abs(x)] ^ (x < 0)))
            return true;
        if(clauses[clause_id].size() == 1)
            return false;
        x = clauses[clause_id][watchs[clause_id].second];
        if(var_assigned[abs(x)] && (var_table[abs(x)] ^ (x < 0)))
            return true;
        return false;
    }
    bool assign_update(int x) {
        vector<pair<int, int>> change_watch;
        vector<int> stay_watch;
        int clause_id;
        for(vector<int>::reverse_iterator p = var_to_watch[x < 0][abs(x)].rbegin(), p_end = var_to_watch[x < 0][abs(x)].rend(); p != p_end; p++) {
            clause_id = *p;
            pair<int, int> watch = watchs[clause_id];
            vector<int> &clause = clauses[clause_id];
            if(set_of_clauses(clause_id)) {
                stay_watch.push_back(clause_id);
                continue;
            }
            if(var_assigned[abs(clause[watch.first])] && var_assigned[abs(clause[watch.second])]) { // conflict
                var_to_watch[x < 0][abs(x)].resize(p_end - p);
                for(int i : stay_watch)
                    var_to_watch[x < 0][abs(x)].push_back(i);
                conflict_clause_id = *p;
                return false;
            }
            int orix = watch.second, not_x = watch.first;
            if(clause[watch.first] == -x) {
                orix = watch.first;
                not_x = watch.second;
            }
            for(int p = watch.second, cnt = 0; true; cnt++) {
                if(cnt) {
                    if(cnt == (int)clause.size()) { // unit_clause
                        watchs[clause_id] = make_pair(not_x, orix);
                        stay_watch.push_back(clause_id);
                        unit_clauses.push_back(clause_id);
                        break;
                    }
                    if(var_assigned[abs(clause[p])] && (var_table[abs(clause[p])] ^ (clause[p] < 0))) { // found true literal
                        watchs[clause_id] = make_pair(not_x, p);
                        var_to_watch[clauses[clause_id][p] > 0][abs(clauses[clause_id][p])].push_back(clause_id);
                        break;
                    }
                    if(!var_assigned[abs(clause[p])] && p != (watchs[clause_id].first ^ watchs[clause_id].second ^ orix)) { // found unassigned literal
                        var_to_watch[clauses[clause_id][p] > 0][abs(clauses[clause_id][p])].push_back(clause_id);
                        watchs[clause_id] = make_pair(not_x, p);
                        break;
                    }
                }
                if(++p == (int)clause.size())
                    p = 0;
            }
        }
        var_to_watch[x < 0][abs(x)].swap(stay_watch);
        return true;
    }

    // initialize
    void init(const char *DIMACS_cnf_file) {
        string out_file = DIMACS_cnf_file;
        out_file.resize(out_file.size() - 3);
        out_file += "sat";
        out.open(out_file.c_str(), ios::out);

        parse_DIMACS_CNF(clauses, maxVarIndex, DIMACS_cnf_file);
        // learn_size_limit = maxVarIndex;
        restart_tag = 0;
        ori_clauses_size = clauses.size();
        init_clauses_size = clauses.size();
        set_of_literal_cnt = 0;
        var_assigned.resize(maxVarIndex + 1, false);
        var_table.resize(maxVarIndex + 1, false);
        
        // VSIDS
        literal_cnt.resize(maxVarIndex + 1);
        posc.resize(maxVarIndex + 1, 0);
        negc.resize(maxVarIndex + 1, 0);

        two_literals_init();
        var_assigned_level.resize(maxVarIndex + 1, 0);
        var_imply_by_clause.resize(maxVarIndex + 1, -1);
        conflict_var_inqueue.resize(maxVarIndex + 1, 0);
        var_assigned_order.resize(maxVarIndex + 1, -1);
        VSIDS_reload();
    }

    // restart
    bool restart_tag;
    void restart() {
        restart_rate = min(1.5 * restart_rate, static_cast<double>(restart_rate) + 50000);
        reduce_learned_clause();
        ori_clauses_size = clauses.size();
        unit_clauses.clear();
        restart_tag = 0;
        set_of_literal_cnt = 0;
        fill_n(var_assigned.begin(), maxVarIndex + 1, false);
        fill_n(var_table.begin(), maxVarIndex + 1, false);

        two_literals_init();
        fill_n(var_assigned_level.begin(), maxVarIndex + 1, 0);
        fill_n(var_imply_by_clause.begin(), maxVarIndex + 1, -1);
        VSIDS_reload();
    }
    
    // VSIDS
    #define divide_constant 500000000LL
    vector<int> posc, negc;
    vector<int> literal_cnt;
    set<pair<int, int>> ranking;
    void VSIDS_reload() {
        ranking.clear();
        for(int i = 1; i <= maxVarIndex; i++)
            if(!var_assigned[i])
                ranking.insert(make_pair(literal_cnt[i], i));
    }
    int get_VSIDS() {
        static int flag = 0;
        static int counter = divide_constant - 1;
        if((++counter) == divide_constant || ranking.rbegin() -> first > 4096) {
            if(flag) {
                int x = rand() & 1; ++x; x = 1;
                for(int &i : literal_cnt)
                    i >>= x;
            }
            VSIDS_reload();
            flag = 1;
            counter = 0;
        }
        int re = ranking.rbegin() -> second;
        return re;
    }

    // assigns
    bool assign(int x, int level) {
        ranking.erase(make_pair(literal_cnt[abs(x)], abs(x)));
        var_assigned[abs(x)] = 1;
        set_of_literal_cnt++;
        var_table[abs(x)] = (x > 0);
        var_assigned_level[abs(x)] = level;
        var_assigned_order[abs(x)] = set_of_literal_cnt;
        return assign_update(x);
    }
    bool assign_unit_clause(int clause_id, vector<int> &assigns, int level) {
        if(var_assigned[abs(clauses[clause_id][watchs[clause_id].first])])
            return var_table[abs(clauses[clause_id][watchs[clause_id].first])] ^ (clauses[clause_id][watchs[clause_id].first] < 0);
        assigns.push_back(clauses[clause_id][watchs[clause_id].first]);
        var_imply_by_clause[abs(clauses[clause_id][watchs[clause_id].first])] = clause_id;
        return assign(clauses[clause_id][watchs[clause_id].first], level);
    }
    void restore(int literal_id) {
        if(restart_tag) return;
        ranking.insert(make_pair(literal_cnt[abs(literal_id)], abs(literal_id)));
        var_assigned[abs(literal_id)] = 0;
        --set_of_literal_cnt;
        return;
    }
    void restores(vector<int> &assigns) {
        if(restart_tag) return;
        for(int literal_id : assigns)
            restore(literal_id);
    }
    
    // DPLL
    bool single_unit(int level, vector<int> &assigns) {
        int clause_id = unit_clauses[0];
        unit_clauses.pop_back();
        if(!assign_unit_clause(clause_id, assigns, level - 1))
            return false;
        return true;
    }
    bool assign_unit_clauses(int level, vector<int> &assigns) {
        level--;
        while(!unit_clauses.empty()) {
            int clause_id = unit_clauses.back();
            unit_clauses.pop_back();
            if(!assign_unit_clause(clause_id, assigns, level)) {
                unit_clauses.clear();
                if(level != 0)
                    conflict_learning(level);
                restores(assigns);
                return false;
            }
        }
        return true;
    }
    bool DPLL(int assign_precision, int level) {
        vector<int> assigns;
        if(!assign_unit_clauses(level, assigns))
            return false;
        if(check_all_sat())
            return true;
        for(int x = get_VSIDS(), i = 0; 1; x = get_VSIDS()) {
            var_imply_by_clause[x] = -1;
            bool flag = posc[x] > negc[x];
            if(flag) {
                while(!var_assigned[x]) {
                    return_to_level = level;
                    if(assign(x, level) && DPLL(i + 1, level + 1))
                        return true;
                    restore(x);
                    if(return_to_level < level) {
                        restores(assigns);
                        return false;
                    }
                    if(unit_clauses.empty() && !try_other_var) 
                        break;
                    if(try_other_var) {
                        ranking.erase(make_pair(literal_cnt[x], x));
                        literal_cnt[x] /= 2;
                        ranking.insert(make_pair(literal_cnt[x], x));
                        try_other_var = 0;
                    }
                    if(!assign_unit_clauses(level, assigns))
                        return false;
                    if(check_all_sat())
                        return true;
                }
                if(var_assigned[x])
                    continue;
            }
            while(!var_assigned[x]) {
                return_to_level = level;
                if(assign(-x, level) && DPLL(i + 1, level + 1))
                    return true;
                restore(-x);
                if(return_to_level < level) {
                    restores(assigns);
                    return false;
                }
                if(unit_clauses.empty() && !try_other_var) 
                    break;
                if(try_other_var) {
                    ranking.erase(make_pair(literal_cnt[x], x));
                    literal_cnt[x] /= 2;
                    ranking.insert(make_pair(literal_cnt[x], x));
                    try_other_var = 0;
                }
                if(!assign_unit_clauses(level, assigns))
                    return false;
                if(check_all_sat())
                    return true;
            }
            if(var_assigned[x])
                continue;
            if(!flag) {
                while(!var_assigned[x]) {
                    return_to_level = level;
                    if(assign(x, level) && DPLL(i + 1, level + 1))
                        return true;
                    restore(x);
                    if(return_to_level < level) {
                        restores(assigns);
                        return false;
                    }
                    if(unit_clauses.empty() && !try_other_var)
                        break;
                    if(try_other_var) {
                        ranking.erase(make_pair(literal_cnt[x], x));
                        literal_cnt[x] /= 2;
                        ranking.insert(make_pair(literal_cnt[x], x));
                        try_other_var = 0;
                    }
                    if(!assign_unit_clauses(level, assigns))
                        return false;
                    if(check_all_sat())
                        return true;
                }
                if(var_assigned[x])
                    continue;
            }
            break;
        }
        restores(assigns);
        return_to_level = level;
        return false;
    }

    // main solve
    void solve() {
        for(vector<int> &i : clauses)
            if(i.empty()) { // found empty clause
                out << "s UNSATISFIABLE\n";
                return;
            }
        bool flag = DPLL(0, 1); 
        while(restart_tag) {
            restart();
            flag = DPLL(0, 1);
        }
        if(flag) {
            out << "s SATISFIABLE\n";
            output();
        } else {
            out << "s UNSATISFIABLE\n";
        }
    }
};

