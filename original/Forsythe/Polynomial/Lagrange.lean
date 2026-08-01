import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic

/-!
# Cubic Lagrange interpolation at four real nodes

The API in this file is specialized to `Fin 4`, the finite-node coordinates used in the
Forsythe proof.  Distinctness is expressed by injectivity of the node map; an ordered node map
discharges this hypothesis with `StrictMono.injective`.
-/

set_option autoImplicit false

namespace Forsythe

open scoped BigOperators

noncomputable section

namespace FourNode

open Polynomial

/-- The `i`th cubic cardinal polynomial for the four nodes `lambda`. -/
def cubicLagrangeBasis (lambda : Fin 4 → ℝ) (i : Fin 4) : ℝ[X] :=
  Lagrange.basis Finset.univ lambda i

/-- Evaluation of the `i`th cardinal polynomial at `t`.  These are the coefficients used to
transport every cubic identity from the four principal nodes to an exterior node. -/
def cubicLagrangeCoeff (lambda : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) : ℝ :=
  (cubicLagrangeBasis lambda i).eval t

/-- The numerator in the explicit rational formula for a cubic Lagrange coefficient. -/
def cubicLagrangeNumerator (lambda : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (t - lambda j)

/-- The denominator in the explicit rational formula for a cubic Lagrange coefficient. -/
def cubicLagrangeDenominator (lambda : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (lambda i - lambda j)

/-- The unique cubic interpolant with prescribed values `y` at the four nodes, when the nodes
are distinct.  The definition is total even when nodes coincide. -/
def cubicLagrangeInterpolate (lambda : Fin 4 → ℝ) (y : Fin 4 → ℝ) : ℝ[X] :=
  Lagrange.interpolate Finset.univ lambda y

/-- Product formula for the cardinal coefficients. -/
theorem cubicLagrangeCoeff_eq_prod (lambda : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    cubicLagrangeCoeff lambda t i =
      ∏ j ∈ Finset.univ.erase i, (lambda i - lambda j)⁻¹ * (t - lambda j) := by
  simp [cubicLagrangeCoeff, cubicLagrangeBasis, Lagrange.basis,
    Lagrange.basisDivisor, eval_prod]

/-- Explicit numerator-over-denominator formula. -/
theorem cubicLagrangeCoeff_eq_div (lambda : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    cubicLagrangeCoeff lambda t i =
      cubicLagrangeNumerator lambda t i / cubicLagrangeDenominator lambda i := by
  rw [cubicLagrangeCoeff_eq_prod]
  simp only [cubicLagrangeNumerator, cubicLagrangeDenominator, div_eq_mul_inv,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  ring

theorem cubicLagrangeDenominator_ne_zero {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (i : Fin 4) :
    cubicLagrangeDenominator lambda i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [sub_ne_zero]
  exact hlambda.ne (Finset.mem_erase.mp hj).1.symm

/-- The cardinal-polynomial evaluation law. -/
theorem eval_cubicLagrangeBasis {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (i j : Fin 4) :
    (cubicLagrangeBasis lambda i).eval (lambda j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa [cubicLagrangeBasis] using
      (Lagrange.eval_basis_self hlambda.injOn (Finset.mem_univ i))
  · rw [if_neg hij]
    simpa [cubicLagrangeBasis] using
      (Lagrange.eval_basis_of_ne hij (Finset.mem_univ j) :
        (Lagrange.basis Finset.univ lambda i).eval (lambda j) = 0)

/-- Cardinal form stated directly for the scalar coefficients. -/
theorem cubicLagrangeCoeff_at_node {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (i j : Fin 4) :
    cubicLagrangeCoeff lambda (lambda j) i = if i = j then 1 else 0 :=
  eval_cubicLagrangeBasis hlambda i j

theorem natDegree_cubicLagrangeBasis {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (i : Fin 4) :
    (cubicLagrangeBasis lambda i).natDegree = 3 := by
  simpa [cubicLagrangeBasis] using
    (Lagrange.natDegree_basis hlambda.injOn (Finset.mem_univ i))

/-- Expansion of the interpolant in the four cardinal polynomials. -/
theorem cubicLagrangeInterpolate_eq_sum (lambda : Fin 4 → ℝ) (y : Fin 4 → ℝ) :
    cubicLagrangeInterpolate lambda y =
      ∑ i : Fin 4, C (y i) * cubicLagrangeBasis lambda i := by
  simp [cubicLagrangeInterpolate, Lagrange.interpolate_apply, cubicLagrangeBasis]

/-- Interpolation takes the prescribed value at each node. -/
theorem eval_cubicLagrangeInterpolate {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (y : Fin 4 → ℝ) (i : Fin 4) :
    (cubicLagrangeInterpolate lambda y).eval (lambda i) = y i := by
  simpa [cubicLagrangeInterpolate] using
    (Lagrange.eval_interpolate_at_node y hlambda.injOn (Finset.mem_univ i))

/-- The four-node interpolant has degree at most three. -/
theorem natDegree_cubicLagrangeInterpolate_le {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (y : Fin 4 → ℝ) :
    (cubicLagrangeInterpolate lambda y).natDegree ≤ 3 := by
  have hdegree := Lagrange.degree_interpolate_le y
    (s := (Finset.univ : Finset (Fin 4))) hlambda.injOn
  have hnat := natDegree_le_of_degree_le hdegree
  simpa [cubicLagrangeInterpolate] using hnat

/-- Four distinct evaluations determine a polynomial of degree at most three. -/
theorem cubic_eq_of_eval_eq {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {f g : ℝ[X]} (hf : f.natDegree ≤ 3) (hg : g.natDegree ≤ 3)
    (heval : ∀ i : Fin 4, f.eval (lambda i) = g.eval (lambda i)) : f = g := by
  apply eq_of_natDegree_lt_card_of_eval_eq f g hlambda heval
  simp only [Fintype.card_fin]
  omega

/-- Characterization and uniqueness of the cubic interpolant. -/
theorem eq_cubicLagrangeInterpolate_of_eval_eq {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (y : Fin 4 → ℝ) {f : ℝ[X]}
    (hf : f.natDegree ≤ 3) (heval : ∀ i : Fin 4, f.eval (lambda i) = y i) :
    f = cubicLagrangeInterpolate lambda y := by
  apply cubic_eq_of_eval_eq hlambda hf (natDegree_cubicLagrangeInterpolate_le hlambda y)
  intro i
  rw [heval i, eval_cubicLagrangeInterpolate hlambda y i]

/-- Every polynomial of degree at most three is reconstructed from its four nodal values. -/
theorem eq_cubicLagrangeInterpolate {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (f : ℝ[X]) (hf : f.natDegree ≤ 3) :
    f = cubicLagrangeInterpolate lambda (fun i ↦ f.eval (lambda i)) :=
  eq_cubicLagrangeInterpolate_of_eval_eq hlambda _ hf fun _ ↦ rfl

/-- Scalar interpolation identity at an arbitrary real point.  This is the form used for
first-variation cancellation at an exterior node. -/
theorem eval_eq_sum_cubicLagrangeCoeff_mul_eval {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (f : ℝ[X]) (hf : f.natDegree ≤ 3) (t : ℝ) :
    f.eval t = ∑ i : Fin 4, cubicLagrangeCoeff lambda t i * f.eval (lambda i) := by
  calc
    f.eval t =
        (cubicLagrangeInterpolate lambda (fun i ↦ f.eval (lambda i))).eval t :=
      congrArg (eval t) (eq_cubicLagrangeInterpolate hlambda f hf)
    _ = ∑ i : Fin 4, cubicLagrangeCoeff lambda t i * f.eval (lambda i) := by
      rw [cubicLagrangeInterpolate_eq_sum, eval_finsetSum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [cubicLagrangeCoeff, mul_comm]

/-- The four cardinal coefficients form a partition of unity. -/
theorem sum_cubicLagrangeCoeff {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (t : ℝ) :
    ∑ i : Fin 4, cubicLagrangeCoeff lambda t i = 1 := by
  simpa using (eval_eq_sum_cubicLagrangeCoeff_mul_eval hlambda (1 : ℝ[X]) (by simp) t).symm

/-- Cubic moment reproduction by the cardinal coefficients. -/
theorem sum_cubicLagrangeCoeff_mul_pow {lambda : Fin 4 → ℝ}
    (hlambda : Function.Injective lambda) (t : ℝ) {m : ℕ} (hm : m ≤ 3) :
    ∑ i : Fin 4, cubicLagrangeCoeff lambda t i * (lambda i) ^ m = t ^ m := by
  have h := eval_eq_sum_cubicLagrangeCoeff_mul_eval hlambda (X ^ m) (by simpa using hm) t
  simpa using h.symm

/-- Ordered nodes are, in particular, valid distinct interpolation nodes. -/
theorem eval_cubicLagrangeInterpolate_of_strictMono {lambda : Fin 4 → ℝ}
    (hlambda : StrictMono lambda) (y : Fin 4 → ℝ) (i : Fin 4) :
    (cubicLagrangeInterpolate lambda y).eval (lambda i) = y i :=
  eval_cubicLagrangeInterpolate hlambda.injective y i

end FourNode

end

end Forsythe
