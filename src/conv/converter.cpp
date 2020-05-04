#include "conv/converter.h"
#include "common/var.h"
#include "icsp/bool_literal.h"
#include "icsp/linear_sum.h"
#include "icsp/linear_literal.h"

namespace csugar
{

std::vector<Clause> Converter::ConvertConstraint(std::shared_ptr<Expr> expr, bool negative)
{
    std::vector<Clause> clauses;

    while (true) {
        if (expr->type() == kConstantBool) {
            bool actual = (expr->AsConstantBool() != negative);
            if (actual) {
                // satisfied; do nothing
            } else {
                // unsatisfied
                clauses.push_back(Clause());
            }
            break;
        } else if (expr->type() == kVariableBool) {
            clauses.push_back(Clause(std::make_shared<BoolLiteral>(icsp_.GetBoolVar(expr->VariableName()), negative)));
            break;
        } else if (expr->IsLogical()) {
            if (expr->type() == kNot) {
                expr = (*expr)[0];
                negative = !negative;
                continue;
            }
            expr = ConvertLogical(expr, negative, clauses);
            if (!expr) break;
        } else if (expr->IsComparison()) {
            expr = ConvertComparison(expr, negative, clauses);
            if (!expr) break;
        }
    }
    return clauses;
}
std::shared_ptr<Expr> Converter::ConvertLogical(std::shared_ptr<Expr> expr, bool negative, std::vector<Clause> &clauses)
{
    if (expr->type() == kImp) {
        return Expr::Or(Expr::Not((*expr)[0]), (*expr)[1]);
    } else if (expr->type() == kXor) {
        // TODO: this seems inefficient
        return Expr::And(Expr::Or((*expr)[0], (*expr)[1]), Expr::Or(Expr::Not((*expr)[0]), Expr::Not((*expr)[1])));
    } else if (expr->type() == kIff) {
        // TODO: this seems inefficient
        return Expr::And(Expr::Or((*expr)[0], Expr::Not((*expr)[1])), Expr::Or(Expr::Not((*expr)[0]), (*expr)[1]));
    } else if ((expr->type() == kAnd && !negative) || (expr->type() == kOr && negative)) {
        for (int i = 0; i < expr->size(); ++i) {
            auto clauses_sub = ConvertConstraint((*expr)[i], negative);
            clauses.insert(clauses.end(), clauses_sub.begin(), clauses_sub.end());
        }
        return std::shared_ptr<Expr>(nullptr);
    } else if ((expr->type() == kAnd && negative) || (expr->type() == kOr && !negative)) {
        auto clauses_sub = ConvertDisj(expr, negative);
        clauses.insert(clauses.end(), clauses_sub.begin(), clauses_sub.end());
    } else {
        // TODO: error
    }
}
std::vector<Clause> Converter::ConvertDisj(std::shared_ptr<Expr> expr, bool negative)
{
    std::vector<Clause> clauses;
    if (expr->size() == 0) {
        clauses.push_back(Clause());
    } else if (expr->size() == 1) {
        clauses = ConvertConstraint((*expr)[0], negative);
    } else {
        Clause aux_clause;
        for (int i = 0; i < expr->size(); ++i) {
            auto clauses_sub = ConvertConstraint((*expr)[i], negative);
            if (clauses_sub.size() == 0) {
                return clauses_sub;
            } else if (clauses_sub.size() == 1) {
                Clause &c = clauses_sub[0];
                for (int j = 0; j < c.size(); ++j) {
                    aux_clause.Add(c[j]);
                }
            } else {
                auto v = icsp_.AuxiliaryBoolVar();
                auto v0 = std::make_shared<BoolLiteral>(v, false);
                auto v1 = std::make_shared<BoolLiteral>(v, true);
                aux_clause.Add(v0);

                // TODO: EQUIV_TRANSLATION?
                for (int j = 0; j < clauses_sub.size(); ++j) {
                    auto c = clauses_sub[j];
                    c.Add(v1);
                    clauses.push_back(c);
                }
            }
        }
    }
    return clauses;
}
std::shared_ptr<Expr> Converter::ConvertComparison(std::shared_ptr<Expr> expr, bool negative, std::vector<Clause> &clauses)
{
    // TODO: NORMALIZE_LINEARSUM?
    if (true) {

    }

    std::vector<Clause> clauses_sub;
    if ((expr->type() == kEq && !negative) || (expr->type() == kNe && negative)) {
        clauses_sub = ConvertComparison((*expr)[0], (*expr)[1], kLitEq);
    } else if ((expr->type() == kNe && !negative) || (expr->type() == kEq && negative)) {
        clauses_sub = ConvertComparison((*expr)[0], (*expr)[1], kLitNe);
    } else if ((expr->type() == kLe && !negative) || (expr->type() == kGt && negative)) {
        clauses_sub = ConvertComparison((*expr)[0], (*expr)[1], kLitLe);
    } else if ((expr->type() == kLt && !negative) || (expr->type() == kGe && negative)) {
        clauses_sub = ConvertComparison(Expr::Make(kAdd, {(*expr)[0], Expr::ConstInt(1)}), (*expr)[1], kLitLe);
    } else if ((expr->type() == kGe && !negative) || (expr->type() == kLt && negative)) {
        clauses_sub = ConvertComparison((*expr)[0], (*expr)[1], kLitGe);
    } else if ((expr->type() == kGt && !negative) || (expr->type() == kLe && negative)) {
        clauses_sub = ConvertComparison((*expr)[0], Expr::Make(kAdd, {(*expr)[1], Expr::ConstInt(1)}), kLitGe);
    }
    clauses.insert(clauses.end(), clauses_sub.begin(), clauses_sub.end());
    return std::shared_ptr<Expr>(nullptr);
}
std::vector<Clause> Converter::ConvertComparison(std::shared_ptr<Expr> x, std::shared_ptr<Expr> y, LinearLiteralOp op)
{
    LinearSum e = ConvertFormula(Expr::Make(kSub, {x, y}));
    e.Factorize();
}
LinearSum Converter::ConvertFormula(std::shared_ptr<Expr> expr)
{
    if (auto v = GetEquivalence(expr)) {
        return LinearSum(v);
    } else if (expr->type() == kConstantInt) {
        return LinearSum(expr->AsConstantInt());
    } else if (expr->type() == kVariableInt) {
        if (!icsp_.HasIntVar(expr->VariableName())) {
            // TODO: error
        }
        return LinearSum(icsp_.GetIntVar(expr->VariableName()));
    } else if (expr->type() == kAdd) {
        LinearSum ret(0);
        for (int i = 0; i < expr->size(); ++i) {
            ret += ConvertFormula((*expr)[i]);
        }
        return ret;
    } else if (expr->type() == kSub) {
        if (expr->size() == 0) {
            // TODO: error
        } else if (expr->size() == 1) {
            LinearSum ret = ConvertFormula((*expr)[0]);
            ret *= -1;
            return ret;
        } else {
            LinearSum ret = ConvertFormula((*expr)[0]);
            for (int i = 1; i < expr->size(); ++i) {
                ret -= ConvertFormula((*expr)[i]);
            }
            return ret;
        }
    } else if (expr->type() == kIf) {
        auto x1 = (*expr)[0], x2 = (*expr)[1], x3 = (*expr)[2];
        LinearSum s2 = ConvertFormula(x2), s3 = ConvertFormula(x3);
        std::unique_ptr<Domain> d2 = s2.GetDomain(), d3 = s3.GetDomain();
        std::unique_ptr<Domain> d = d2->Cup(d3);
        auto v = icsp_.AuxiliaryIntVar(std::move(d));
        auto x = Expr::VarInt(v->name());
        auto eq = Expr::And(Expr::Or(Expr::Not(x1), Expr::Eq(x, x2)), Expr::Or(x1, Expr::Eq(x, x3)));
        ConvertConstraint(eq);
        AddEquivalence(v, expr);
        return LinearSum(v);
    } else if (expr->type() == kMul || expr->type() == kDiv || expr->type() == kMod
            || expr->type() == kPow || expr->type() == kMin || expr->type() == kMax) {
        // TODO: not implemented yet
    } else {
        // TODO: error
    }
}

}