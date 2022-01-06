#include<iostream>
#include<vector>
#include<time.h>
#include<algorithm>
using namespace std;
int main() {
    int n, m;
    cin >> n >> m;
    vector<pair<int, int>> v;
    for(int i = 0; i < n; i++) {
        for(int j = 0; j < i; j++) {
            v.push_back(make_pair(j, i));
        }
    }
    srand(time(0));
    random_shuffle(v.begin(), v.end());
    v.resize(m);
    cout << n << ' ' << m << endl;
    for(int i = 0; i < m; i++)
        cout << v[i].first + 1 << ' ' << v[i].second + 1 << endl;
}
