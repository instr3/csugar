#pragma once

#include <vector>
#include <map>
#include <string>

#include "icsp/clause.h"
#include "common/var.h"
#include "common/domain.h"

namespace csugar {

class ICSP {
public:
    ICSP() : auxiliary_id_(0) {}

    void AddClause(const Clause& clause) { clauses_.push_back(clause); }
    void AddClause(Clause&& clause) { clauses_.push_back(clause); }
    void AddBoolVar(std::shared_ptr<BoolVar> var);
    void AddIntVar(std::shared_ptr<IntVar> var);

    int NumClauses() const { return clauses_.size(); }
    Clause& GetClause(int i) { return clauses_[i]; }
    const Clause& GetClause(int i) const { return clauses_[i]; }

    bool HasBoolVar(const std::string& name);
    std::shared_ptr<BoolVar> GetBoolVar(const std::string& name);
    bool HasIntVar(const std::string& name);
    std::shared_ptr<IntVar> GetIntVar(const std::string& name);

    std::shared_ptr<BoolVar> AuxiliaryBoolVar();
    std::shared_ptr<IntVar> AuxiliaryIntVar(std::unique_ptr<Domain>&& domain);

private:
    std::string AuxiliaryVarName() const;

    std::vector<Clause> clauses_;
    std::vector<std::shared_ptr<BoolVar>> bool_vars_;
    std::vector<std::shared_ptr<IntVar>> int_vars_;
    std::map<std::string, std::shared_ptr<BoolVar>> bool_var_map_;
    std::map<std::string, std::shared_ptr<IntVar>> int_var_map_;
    int auxiliary_id_;
};

}
