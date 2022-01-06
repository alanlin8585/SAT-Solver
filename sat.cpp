#include <iostream>
#include "sat.hpp"
using namespace std;

int main(int argv, char *argc[]) {
    sat solver;
    solver.init(argc[1]);
    solver.solve();
}
