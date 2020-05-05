#include "common/interval_domain.h"

#include <memory>
#include <algorithm>
#include <vector>

namespace csugar {

IntervalDomain::~IntervalDomain() {
}
// TODO: refined domain?
int IntervalDomain::GetLowerBound() const {
    return lb_;
}
int IntervalDomain::GetUpperBound() const {
    return ub_;
}
std::vector<int> IntervalDomain::Enumerate() const {
    std::vector<int> ret;
    for (int i = lb_; i <= ub_; ++i) {
        ret.push_back(i);
    }
    return ret;
}
std::unique_ptr<Domain> IntervalDomain::Add(const std::unique_ptr<Domain>& other) const {
    return std::make_unique<IntervalDomain>(IntervalDomain(lb_ + other->GetLowerBound(), ub_ + other->GetUpperBound()));
}
std::unique_ptr<Domain> IntervalDomain::Sub(const std::unique_ptr<Domain>& other) const {
    return std::make_unique<IntervalDomain>(IntervalDomain(lb_ - other->GetUpperBound(), ub_ - other->GetLowerBound()));
}
std::unique_ptr<Domain> IntervalDomain::Mul(int other) const {
    if (other >= 0) {
        return std::make_unique<IntervalDomain>(IntervalDomain(lb_ * other, ub_ * other));
    } else {
        return std::make_unique<IntervalDomain>(IntervalDomain(ub_ * other, lb_ * other));
    }
}
std::unique_ptr<Domain> IntervalDomain::Cup(const std::unique_ptr<Domain>& other) const {
    return std::make_unique<IntervalDomain>(IntervalDomain(std::min(lb_, other->GetLowerBound()), std::max(ub_, other->GetUpperBound())));
}

}
