import Forsythe.Polynomial.Quadratic

/-!
# Conditional factor variation

This is the algebraic last step in the factor-variation argument.  The later
compactness layer supplies the uniform coefficient bound, the coercivity
constant, and the upper estimate obtained from the three-step identity.
-/

set_option autoImplicit false

namespace Forsythe
namespace Arnoldi

/-- A uniformly coercive quadratic estimate and its three-step upper bound
control the concrete product-norm distance between two monic factors.

The coefficient-bound hypotheses are deliberately explicit: in the complete
proof they are used to produce `hupper` uniformly over the cluster set. -/
theorem factor_variation_of_coercive
    (p q : MonicQuadratic) (kappa M C epsilon energy : ℝ)
    (hkappa : 0 < kappa)
    (hM : 0 ≤ M)
    (hC : 0 ≤ C)
    (hepsilon : 0 ≤ epsilon)
    (hpBound : ‖p.coeffPair‖ ≤ M)
    (hqBound : ‖q.coeffPair‖ ≤ M)
    (hcoercive : kappa * p.coeffDist q ^ 2 ≤ energy)
    (hupper : 0 ≤ M ∧ ‖p.coeffPair‖ ≤ M ∧ ‖q.coeffPair‖ ≤ M →
      energy ≤ kappa * C * epsilon * p.coeffDist q) :
    p.coeffDist q ≤ C * epsilon := by
  have hdist : 0 ≤ p.coeffDist q := MonicQuadratic.coeffDist_nonneg p q
  have hupper' : energy ≤ kappa * C * epsilon * p.coeffDist q :=
    hupper ⟨hM, hpBound, hqBound⟩
  by_cases hzero : p.coeffDist q = 0
  · rw [hzero]
    positivity
  · have hpos : 0 < p.coeffDist q := lt_of_le_of_ne hdist (Ne.symm hzero)
    have hmul :
        (kappa * p.coeffDist q) * p.coeffDist q ≤
          (kappa * p.coeffDist q) * (C * epsilon) := by
      calc
        (kappa * p.coeffDist q) * p.coeffDist q =
            kappa * p.coeffDist q ^ 2 := by ring
        _ ≤ energy := hcoercive
        _ ≤ kappa * C * epsilon * p.coeffDist q := hupper'
        _ = (kappa * p.coeffDist q) * (C * epsilon) := by ring
    by_contra hnot
    have hstrict : C * epsilon < p.coeffDist q := lt_of_not_ge hnot
    have := mul_lt_mul_of_pos_left hstrict (mul_pos hkappa hpos)
    exact (not_lt_of_ge hmul) this

end Arnoldi
end Forsythe
