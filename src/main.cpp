#include <string>
#include <iostream>
#include <utility>
#include <vector>
#include <cstdlib>
#include <map>

#include "integrated/integrated.h"

using namespace csugar;

std::vector<std::string> Tokenize(const std::string& s) {
    std::vector<std::string> ret;
    std::string token;
    for (int i = 0; i < s.size(); ++i) {
        if (s[i] == ' ') {
            if (token.size() > 0) ret.push_back(token);
            token.clear();
        } else {
            token.push_back(s[i]);
        }
    }
    if (token.size() > 0) ret.push_back(token);
    return ret;
}
bool IsComment(const std::string& s) {
    return s.size() >= 1 && s[0] == ';';
}

void InputCSP(IntegratedCSPSolver& solver, bool& has_answer_key, std::vector<std::string>& answer_keys, int& max_answers) {
    std::string line;

    while (std::getline(std::cin, line)) {
        if (line.size() == 0 || IsComment(line)) {
            continue;
        } else if (line[0] == '#') {
            auto keys = Tokenize(line.substr(1));
            answer_keys.insert(answer_keys.end(), keys.begin(), keys.end());
            has_answer_key = true;
		} else if (line[0] == '$') {
			max_answers = std::stoi(line.substr(1));
        } else {
            solver.Parse(line);
        }
    }
}

void SolveLocalMaximal(IntegratedCSPSolver& solver,
    std::vector<std::string>& answer_keys) {
    CSPAnswer answer = solver.Solve();
    solver.SetTargetVars(answer_keys);

    if (!answer.IsSat()) {
        std::cout << "unsat" << std::endl;
        return;
    }

    std::map<std::string, bool> not_refuted_bool;
    for (auto& name : answer_keys) {
        if (solver.HasBoolVar(name)) {
            not_refuted_bool.insert({ name, answer.GetBool(name) });
        }
        else {
            std::cout << "bool variable " << name << " not found" << std::endl;
            return;
        }
    }
    while (true) {
        std::vector<std::shared_ptr<Expr>> refuting_exprs;
        for (auto it = not_refuted_bool.begin(); it != not_refuted_bool.end(); ) {
            if (answer.GetBool(it->first) == true) {
                solver.AddConstraint(Expr::VarBool(solver.GetBoolVar(it->first)));
                it = not_refuted_bool.erase(it);
            }
            else {
                refuting_exprs.push_back(Expr::VarBool(solver.GetBoolVar(it->first)));
                ++it;
            }
        }
        if (not_refuted_bool.empty()) break;
        solver.AddConstraint(std::make_shared<Expr>(kOr, refuting_exprs));
        answer = solver.Solve();
        if (!answer.IsSat()) break;
    }
    std::cout << "sat" << std::endl;
    for (auto& p : not_refuted_bool) {
        std::cout << p.first << ' ' << (p.second ? "true" : "false") << std::endl;
    }
}

void SolveIrrefutably(IntegratedCSPSolver& solver,
                      std::vector<std::string>& answer_keys) {
    CSPAnswer answer = solver.Solve();
    solver.SetTargetVars(answer_keys);

    if (!answer.IsSat()) {
        std::cout << "unsat" << std::endl;
        return;
    }

    std::map<std::string, bool> not_refuted_bool;
    std::map<std::string, int> not_refuted_int;
    for (auto& name : answer_keys) {
        if (solver.HasBoolVar(name)) {
            not_refuted_bool.insert({name, answer.GetBool(name)});
        } else if (solver.HasIntVar(name)) {
            not_refuted_int.insert({name, answer.GetInt(name)});
        } else {
            std::cout << "variable " << name << " not found" << std::endl;
            return;
        }
    }
    while (true) {
        std::vector<std::shared_ptr<Expr>> refuting_exprs;
        for (auto& p : not_refuted_bool) {
            refuting_exprs.push_back(Expr::Make(kXor, {Expr::VarBool(solver.GetBoolVar(p.first)), Expr::ConstBool(p.second)}));
        }
        for (auto& p : not_refuted_int) {
            refuting_exprs.push_back(Expr::Make(kNe, {Expr::VarInt(solver.GetIntVar(p.first)), Expr::ConstInt(p.second)}));
        }
        solver.AddConstraint(std::make_shared<Expr>(kOr, refuting_exprs));
        
        answer = solver.Solve();
        if (!answer.IsSat()) break;
    
        for (auto it = not_refuted_bool.begin(); it != not_refuted_bool.end(); ) {
            if (answer.GetBool(it->first) != it->second) {
                it = not_refuted_bool.erase(it);
            } else {
                ++it;
            }
        }
        for (auto it = not_refuted_int.begin(); it != not_refuted_int.end(); ) {
            if (answer.GetInt(it->first) != it->second) {
                it = not_refuted_int.erase(it);
            } else {
                ++it;
            }
        }
    }
    std::cout << "sat" << std::endl;
    for (auto& p : not_refuted_bool) {
        std::cout << p.first << ' ' << (p.second ? "true" : "false") << std::endl;
    }
    for (auto& p : not_refuted_int) {
        std::cout << p.first << ' ' << p.second << std::endl;
    }
}

void OutputAnswer(IntegratedCSPSolver& solver, std::vector<std::string>& answer_keys, CSPAnswer& answer) {

	for (auto& name : answer_keys) {
		if (solver.HasBoolVar(name)) {
			std::cout << name << ' ' << (answer.GetBool(name) ? "true" : "false") << std::endl;
		}
		else if (solver.HasIntVar(name)) {
			std::cout << name << ' ' << answer.GetInt(name) << std::endl;
		}
		else {
			std::cout << "variable " << name << " not found" << std::endl;
			return;
		}
	}
	std::cout << "$" << std::endl;
}

void FindAllSolutions(IntegratedCSPSolver& solver,
	std::vector<std::string>& answer_keys,
	int max_solutions
	) {
	CSPAnswer answer = solver.Solve();
	solver.SetTargetVars(answer_keys);
	if (max_solutions == -1)
		max_solutions = INT32_MAX;
	if (!answer.IsSat()) {
		std::cout << "unsat" << std::endl;
		return;
	}
	std::cout << "ans 0" << std::endl;
	OutputAnswer(solver, answer_keys, answer);
	std::set<std::string> not_refuted_bool;
	std::set<std::string> not_refuted_int;
	for (auto& name : answer_keys) {
		if (solver.HasBoolVar(name)) {
			not_refuted_bool.insert(name);
		}
		else if (solver.HasIntVar(name)) {
			not_refuted_int.insert(name);
		}
		else {
			std::cout << "variable " << name << " not found" << std::endl;
			return;
		}
	}
	for (int i = 1; i < max_solutions; ++i) {
		std::vector<std::shared_ptr<Expr>> refuting_exprs;
		for (auto& p : not_refuted_bool) {
			refuting_exprs.push_back(Expr::Make(kXor, { Expr::VarBool(solver.GetBoolVar(p)), Expr::ConstBool(answer.GetBool(p)) }));
		}
		for (auto& p : not_refuted_int) {
			refuting_exprs.push_back(Expr::Make(kNe, { Expr::VarInt(solver.GetIntVar(p)), Expr::ConstInt(answer.GetInt(p)) }));
		}
		solver.AddConstraint(std::make_shared<Expr>(kOr, refuting_exprs));

		answer = solver.Solve();
		if (!answer.IsSat()) break;

		std::cout << "ans " << i << std::endl;
		OutputAnswer(solver, answer_keys, answer);
	}
    std::cout << "unsat" << std::endl;
}

void FindAnswer(IntegratedCSPSolver& solver) {
    CSPAnswer answer = solver.Solve();

    if (!answer.IsSat()) {
        std::cout << "s UNSATISFIABLE" << std::endl;
        return;
    }

    std::cout << "s SATISFIABLE" << std::endl;
    auto bool_vars = solver.BoolVars();
    for (auto& var : bool_vars) {
        std::cout << "a " << var << '\t' << (answer.GetBool(var) ? "true" : "false") << std::endl;
    }
    auto int_vars = solver.IntVars();
    for (auto& var : int_vars) {
        std::cout << "a " << var << '\t' << answer.GetInt(var) << std::endl;
    }
    std::cout << "a" << std::endl;
}

int main() {
    bool has_answer_key = false;
	int max_answers = 0;
    std::vector<std::string> answer_keys;
    IntegratedCSPSolver solver;
    InputCSP(solver, has_answer_key, answer_keys, max_answers);
    if (max_answers == -2) {
        SolveLocalMaximal(solver, answer_keys);
    } else if (max_answers != 0) {
		FindAllSolutions(solver, answer_keys, max_answers);
	} else if (has_answer_key) {
		SolveIrrefutably(solver, answer_keys);
	} else {
        FindAnswer(solver);
    }

    return 0;
}
