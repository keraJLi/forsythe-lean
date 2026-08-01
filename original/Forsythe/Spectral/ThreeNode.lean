import Forsythe.Polynomial.Quadratic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Rigidity of the three-node weight equations

At three distinct nodes, the three manuscript constraints against
`1`, `p`, and `z p` determine the weights uniquely whenever the two monic
quadratics satisfy `p(lambda i) q(lambda i) = H` with `H ≠ 0`.

The proof follows the determinant argument in polynomial form.  After
multiplying a null weight vector by `p(lambda i)`, its pairings with
`1`, `z`, and the monic quadratic `q` vanish.  The last pairing reduces to
the quadratic moment, so the degree-two Vandermonde matrix is nonsingular.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open scoped BigOperators

noncomputable section

/-- The three scalar constraint values associated with weights on three
nodes. -/
def threeNodeWeightConstraints (lambda : Fin 3 → ℝ) (p : MonicQuadratic)
    (w : Fin 3 → ℝ) : ℝ × (ℝ × ℝ) :=
  (∑ i, w i,
    ∑ i, w i * p.toPolynomial.eval (lambda i),
    ∑ i, w i * (lambda i * p.toPolynomial.eval (lambda i)))

/-- A vector whose pairings with `1`, `z`, and a monic quadratic vanish at
three distinct nodes is zero.  This is the degree-two Vandermonde step. -/
theorem eq_zero_of_threeNode_monicQuadratic_moments
    (lambda : Fin 3 → ℝ) (hlambda : Function.Injective lambda)
    (q : MonicQuadratic) (e : Fin 3 → ℝ)
    (hzero : ∑ i, e i = 0)
    (hone : ∑ i, e i * lambda i = 0)
    (hq : ∑ i, e i * q.toPolynomial.eval (lambda i) = 0) :
    e = 0 := by
  have hexpand :
      (∑ i, e i * q.toPolynomial.eval (lambda i)) =
        (∑ i, e i * lambda i ^ 2) +
          q.linearCoeff * (∑ i, e i * lambda i) +
          q.constantCoeff * (∑ i, e i) := by
    calc
      (∑ i, e i * q.toPolynomial.eval (lambda i)) =
          ∑ i, ((e i * lambda i ^ 2 +
            q.linearCoeff * (e i * lambda i)) +
              q.constantCoeff * e i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [MonicQuadratic.eval]
        ring
      _ = (∑ i, e i * lambda i ^ 2) +
          q.linearCoeff * (∑ i, e i * lambda i) +
          q.constantCoeff * (∑ i, e i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  have htwo : ∑ i, e i * lambda i ^ 2 = 0 := by
    rw [hexpand, hone, hzero] at hq
    simpa using hq
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hlambda
  intro degree
  fin_cases degree
  · simpa using hzero
  · simpa using hone
  · simpa using htwo

/-- Homogeneous form of three-node rigidity for the manuscript constraint
functions `1`, `p`, and `z p`. -/
theorem eq_zero_of_threeNode_weight_constraints
    (lambda : Fin 3 → ℝ) (hlambda : Function.Injective lambda)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hpq : ∀ i, p.toPolynomial.eval (lambda i) *
      q.toPolynomial.eval (lambda i) = H)
    (d : Fin 3 → ℝ)
    (hzero : ∑ i, d i = 0)
    (hp : ∑ i, d i * p.toPolynomial.eval (lambda i) = 0)
    (hlp : ∑ i,
      d i * (lambda i * p.toPolynomial.eval (lambda i)) = 0) :
    d = 0 := by
  let e : Fin 3 → ℝ := fun i => d i * p.toPolynomial.eval (lambda i)
  have hezero : ∑ i, e i = 0 := by
    simpa only [e] using hp
  have heone : ∑ i, e i * lambda i = 0 := by
    rw [show (∑ i, e i * lambda i) =
        ∑ i, d i * (lambda i * p.toPolynomial.eval (lambda i)) by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [e]
      ring]
    exact hlp
  have heq : ∑ i, e i * q.toPolynomial.eval (lambda i) = 0 := by
    calc
      (∑ i, e i * q.toPolynomial.eval (lambda i)) =
          ∑ i, H * d i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [e]
        rw [← hpq i]
        ring
      _ = H * ∑ i, d i := by rw [Finset.mul_sum]
      _ = 0 := by rw [hzero, mul_zero]
  have he := eq_zero_of_threeNode_monicQuadratic_moments
    lambda hlambda q e hezero heone heq
  funext i
  have hei := congrFun he i
  change d i * p.toPolynomial.eval (lambda i) = 0 at hei
  have hpne : p.toPolynomial.eval (lambda i) ≠ 0 := by
    intro hpzero
    have hi := hpq i
    rw [hpzero, zero_mul] at hi
    exact hH hi.symm
  exact (mul_eq_zero.mp hei).resolve_right hpne

/-- Equality of the three constraint values forces equality of the weight
vectors. -/
theorem threeNode_weights_eq_of_constraints_eq
    (lambda : Fin 3 → ℝ) (hlambda : Function.Injective lambda)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hpq : ∀ i, p.toPolynomial.eval (lambda i) *
      q.toPolynomial.eval (lambda i) = H)
    {w u : Fin 3 → ℝ}
    (hsum : (∑ i, w i) = ∑ i, u i)
    (hp : (∑ i, w i * p.toPolynomial.eval (lambda i)) =
      ∑ i, u i * p.toPolynomial.eval (lambda i))
    (hlp : (∑ i, w i *
        (lambda i * p.toPolynomial.eval (lambda i))) =
      ∑ i, u i * (lambda i * p.toPolynomial.eval (lambda i))) :
    w = u := by
  let d : Fin 3 → ℝ := fun i => w i - u i
  have hdzero : ∑ i, d i = 0 := by
    simp only [d, Finset.sum_sub_distrib, hsum, sub_self]
  have hdp : ∑ i, d i * p.toPolynomial.eval (lambda i) = 0 := by
    simp only [d, sub_mul, Finset.sum_sub_distrib, hp, sub_self]
  have hdlp : ∑ i,
      d i * (lambda i * p.toPolynomial.eval (lambda i)) = 0 := by
    simp only [d, sub_mul, Finset.sum_sub_distrib, hlp, sub_self]
  have hd := eq_zero_of_threeNode_weight_constraints
    lambda hlambda p q hH hpq d hdzero hdp hdlp
  funext i
  have hdi := congrFun hd i
  change w i - u i = 0 at hdi
  exact sub_eq_zero.mp hdi

/-- The map collecting the three weight constraints is injective. -/
theorem threeNodeWeightConstraints_injective
    (lambda : Fin 3 → ℝ) (hlambda : Function.Injective lambda)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hpq : ∀ i, p.toPolynomial.eval (lambda i) *
      q.toPolynomial.eval (lambda i) = H) :
    Function.Injective (threeNodeWeightConstraints lambda p) := by
  intro w u hwu
  apply threeNode_weights_eq_of_constraints_eq lambda hlambda p q hH hpq
  · exact congrArg Prod.fst hwu
  · exact congrArg (fun x => x.2.1) hwu
  · exact congrArg (fun x => x.2.2) hwu

/-- Manuscript-facing uniqueness theorem: normalized weights satisfying the
two `p`-orthogonality equations are unique.  No positivity hypothesis on the
weights is needed. -/
theorem threeNode_normalized_orthogonal_weights_unique
    (lambda : Fin 3 → ℝ) (hlambda : Function.Injective lambda)
    (p q : MonicQuadratic) {H : ℝ} (hH : H ≠ 0)
    (hpq : ∀ i, p.toPolynomial.eval (lambda i) *
      q.toPolynomial.eval (lambda i) = H)
    {w u : Fin 3 → ℝ}
    (hwSum : ∑ i, w i = 1)
    (hwP : ∑ i, w i * p.toPolynomial.eval (lambda i) = 0)
    (hwXP : ∑ i, w i *
      (lambda i * p.toPolynomial.eval (lambda i)) = 0)
    (huSum : ∑ i, u i = 1)
    (huP : ∑ i, u i * p.toPolynomial.eval (lambda i) = 0)
    (huXP : ∑ i, u i *
      (lambda i * p.toPolynomial.eval (lambda i)) = 0) :
    w = u := by
  apply threeNode_weights_eq_of_constraints_eq lambda hlambda p q hH hpq
  · rw [hwSum, huSum]
  · rw [hwP, huP]
  · rw [hwXP, huXP]

end

end Spectral
end Forsythe
