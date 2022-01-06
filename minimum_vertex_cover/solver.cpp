#include<iostream>
#include <fstream>
#include<vector>
using namespace std;

vector<vector<int>> cnf;
vector<pair<int, int>> edges(1);
int V, E, K;

void at_most_one(const vector<int> &var) {
    for(int i = 0; i < (int)var.size(); i++)
        for(int j = i + 1; j < (int)var.size(); j++)
            cnf.push_back({-(var[i]), -(var[j])});
}

void exactly_one(const vector<int> &var) {
    cnf.push_back(var);
    at_most_one(var);
}

void encode(const string &in_file) {
    ifstream in(in_file.c_str());
    in >> V >> E >> K;
    for(int i = 0; i < K; i++) {
        vector<int> var;
        for(int j = 1; j <= V; j++)
            var.push_back(i * V + j);
        at_most_one(var);
    }
    for(int i = 1; i <= V; i++) {
        vector<int> var;
        for(int j = 0; j < K; j++)
            var.push_back(j * V + i);
        var.push_back(-(K * V + i));
        exactly_one(var);
    }
    for(int i = 1, u, v; i <= E; i++) {
        in >> u >> v;
        cnf.push_back({K * V + u, K * V + v});
        edges.push_back(make_pair(u, v));
    }
    in.close();
    
    ofstream out("encode.cnf");
    out << "p cnf " << V * (K + 1) << ' ' << cnf.size() << '\n';
    for(vector<int> &i : cnf) {
        for(int j : i)
            out << j << ' ';
        out << "0\n";
    }
    out.close();
}

void solve_sat(const string &solver) {
    string file = (string)"./" + solver + " encode.cnf encode.sat";
    if(solver[0] == '/')
        file = solver + " encode.cnf encode.sat";
    system(file.c_str());
}

void decode(const string &out_file) {
    ifstream in("encode.sat");
    ofstream out(out_file.c_str());
    string s;
    getline(in, s);
    if(s == "s SATISFIABLE" || s == "SAT") {
        if(s != "SAT")
            in >> s;
        vector<int> var_table(V * (K + 1) + 1);
        for(int i = 1, x; i <= V * (K + 1); i++) {
            in >> x;
            if(x > 0)
                var_table[x] = 1;
        }
        cout << '\n';
        vector<int> ans;
        for(int i = 1; i <= V; i++) {
            if(var_table[V * K + i])
                ans.push_back(i);
        }
        for(int i = 0; i < ans.size(); i++)
            out << ans[i] << " \n"[i == ans.size() - 1];
    } else {
        out << "NO\n";
    }
    in.close();
    out.close();
}

int main(int argc, char* argv[]) {
    encode((string)argv[1]);
    solve_sat((string)argv[3]);
    decode((string)argv[2]);
}

