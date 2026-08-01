import Forsythe.FourNode.Rho
import Mathlib.Topology.Algebra.Polynomial

/-!
# Limiting four-node fibers

At a factorization `p q = Pi + tau²`, the candidate `p`-fiber weights are
`tau² (lambda_i-rho) / (E_i p(lambda_i))`.  At a node this is equally
`(lambda_i-rho) q(lambda_i) / E_i`; cubic Lagrange interpolation then gives
normalization and both orthogonality equations exactly, including boundary
states with only three positive weights.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Polynomial Set
open scoped BigOperators

noncomputable section

private theorem coeff_three_cubicLagrangeBasis
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (i : Fin 4) :
    (cubicLagrangeBasis lambda i).coeff 3 = (E lambda i)⁻¹ := by
  have hnat := natDegree_cubicLagrangeBasis hlambda i
  have hlead := Lagrange.leadingCoeff_basis hlambda.injOn
    (Finset.mem_univ i)
  rw [← hnat]
  change (cubicLagrangeBasis lambda i).leadingCoeff = (E lambda i)⁻¹
  simpa [cubicLagrangeBasis, E, cubicLagrangeDenominator,
    Finset.prod_inv_distrib] using hlead

/-- The coefficient of `z³` in the four-node interpolant is the barycentric
sum of its nodal values. -/
theorem sum_eval_div_E_eq_coeff_three
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (f : Polynomial ℝ) (hf : f.natDegree ≤ 3) :
    ∑ i, f.eval (lambda i) / E lambda i = f.coeff 3 := by
  have hinterp := eq_cubicLagrangeInterpolate hlambda f hf
  have hcoeff := congrArg (fun g : Polynomial ℝ ↦ g.coeff 3) hinterp
  rw [cubicLagrangeInterpolate_eq_sum, finsetSum_coeff] at hcoeff
  simp_rw [coeff_C_mul, coeff_three_cubicLagrangeBasis hlambda] at hcoeff
  simpa [div_eq_mul_inv, mul_comm] using hcoeff.symm

theorem sum_sub_div_E
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (rho : ℝ) :
    ∑ i, (lambda i - rho) / E lambda i = 0 := by
  have h := sum_eval_div_E_eq_coeff_three hlambda (X - C rho) (by
    compute_degree
    omega)
  simpa [coeff_sub, coeff_X, coeff_C] using h

theorem sum_lambda_mul_sub_div_E
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (rho : ℝ) :
    ∑ i, lambda i * (lambda i - rho) / E lambda i = 0 := by
  have h := sum_eval_div_E_eq_coeff_three hlambda (X * (X - C rho))
    (by
      compute_degree
      omega)
  have hcoeff : (X * (X - C rho) : Polynomial ℝ).coeff 3 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  rw [hcoeff] at h
  simpa [mul_div_assoc] using h

/-- A monic quadratic multiplied by `z-rho` has barycentric sum one. -/
theorem sum_sub_mul_monicQuadratic_eval_div_E
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (rho : ℝ) (r : MonicQuadratic) :
    ∑ i, (lambda i - rho) * r.toPolynomial.eval (lambda i) / E lambda i = 1 := by
  let f : Polynomial ℝ := (X - C rho) * r.toPolynomial
  have hrDegree : r.toPolynomial.natDegree = 2 := by
    have hle : r.toPolynomial.natDegree ≤ 2 := by
      rw [MonicQuadratic.toPolynomial]
      compute_degree
    have hge : 2 ≤ r.toPolynomial.natDegree :=
      le_natDegree_of_ne_zero (by simp)
    omega
  have hfDegreeEq : f.natDegree = 3 := by
    dsimp only [f]
    rw [(monic_X_sub_C rho).natDegree_mul (MonicQuadratic.monic r),
      natDegree_X_sub_C, hrDegree]
  have hfDegree : f.natDegree ≤ 3 := hfDegreeEq.le
  have h := sum_eval_div_E_eq_coeff_three hlambda f hfDegree
  have hcoeff : f.coeff 3 = 1 := by
    have hmonic : f.Monic :=
      (monic_X_sub_C rho).mul (MonicQuadratic.monic r)
    rw [← hfDegreeEq]
    exact hmonic.coeff_natDegree
  rw [hcoeff] at h
  simpa [f] using h

private theorem nodalQuartic_eval_node (lambda : Fin 4 → ℝ) (i : Fin 4) :
    (nodalQuartic lambda).eval (lambda i) = 0 := by
  rw [nodalQuartic, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- At every node, the limiting factors have product `tau²`. -/
theorem factor_eval_mul_eq_tau_sq
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) (i : Fin 4) :
    p.toPolynomial.eval (lambda i) * q.toPolynomial.eval (lambda i) = tau ^ 2 := by
  have h := congrArg (Polynomial.eval (lambda i)) hfactor
  simpa [eval_mul, eval_add, nodalQuartic_eval_node] using h

theorem factor_eval_ne_zero
    {lambda : Fin 4 → ℝ} {tau : ℝ} (htau : 0 < tau)
    {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) (i : Fin 4) :
    p.toPolynomial.eval (lambda i) ≠ 0 ∧
      q.toPolynomial.eval (lambda i) ≠ 0 := by
  have hprod := factor_eval_mul_eq_tau_sq hfactor i
  have hsq : tau ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt htau)
  exact mul_ne_zero_iff.mp (hprod.symm ▸ hsq)

/-- At every active node the two limiting factors have the same strict sign. -/
theorem factor_eval_same_sign
    {lambda : Fin 4 → ℝ} {tau : ℝ} (htau : 0 < tau)
    {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) (i : Fin 4) :
    (0 < p.toPolynomial.eval (lambda i) ∧
        0 < q.toPolynomial.eval (lambda i)) ∨
      (p.toPolynomial.eval (lambda i) < 0 ∧
        q.toPolynomial.eval (lambda i) < 0) := by
  rw [← mul_pos_iff]
  rw [factor_eval_mul_eq_tau_sq hfactor i]
  positivity

/-- Candidate weights for the fiber whose Arnoldi polynomial is `p`. -/
def fiberWeight (lambda : Fin 4 → ℝ) (tau rho : ℝ)
    (p : MonicQuadratic) (i : Fin 4) : ℝ :=
  tau ^ 2 * (lambda i - rho) /
    (E lambda i * p.toPolynomial.eval (lambda i))

theorem fiberWeight_eq_zero_iff
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) (i : Fin 4) :
    fiberWeight lambda tau rho p i = 0 ↔ lambda i = rho := by
  have hE := E_ne_zero hlambda i
  have hp := (factor_eval_ne_zero htau hfactor i).1
  have htauSq : tau ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt htau)
  rw [fiberWeight]
  simp only [div_eq_zero_iff, mul_eq_zero, htauSq, hE, hp, or_false, false_or,
    sub_eq_zero]

/-- At the factorization nodes, the rational `p`-fiber weight is the cubic
barycentric expression involving the other factor `q`. -/
theorem fiberWeight_eq_otherFactor
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) (i : Fin 4) :
    fiberWeight lambda tau rho p i =
      (lambda i - rho) * q.toPolynomial.eval (lambda i) / E lambda i := by
  have hE := E_ne_zero hlambda i
  have hp := (factor_eval_ne_zero htau hfactor i).1
  have hnode := factor_eval_mul_eq_tau_sq hfactor i
  rw [fiberWeight]
  field_simp [hE, hp]
  rw [← hnode]
  ring

theorem sum_fiberWeight
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) :
    ∑ i, fiberWeight lambda tau rho p i = 1 := by
  simp_rw [fiberWeight_eq_otherFactor hlambda htau hfactor]
  exact sum_sub_mul_monicQuadratic_eval_div_E hlambda rho q

/-- Package candidate weights once nonnegativity and the three-positive
condition have been checked. -/
def fiberPoint
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (tau : ℝ) (htau : 0 < tau) (rho : ℝ) (p q : MonicQuadratic)
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hnonneg : ∀ i, 0 ≤ fiberWeight lambda tau rho p i)
    (hpositive : 3 ≤
      (Finset.univ.filter fun i ↦ 0 < fiberWeight lambda tau rho p i).card) :
    Weights where
  weight := fiberWeight lambda tau rho p
  nonneg := hnonneg
  sum_eq_one := sum_fiberWeight hlambda htau hfactor
  three_le_card_positive := hpositive

@[simp]
theorem fiberPoint_weight
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (tau : ℝ) (htau : 0 < tau) (rho : ℝ) (p q : MonicQuadratic)
    (hfactor) (hnonneg) (hpositive) (i : Fin 4) :
    fiberPoint lambda hlambda tau htau rho p q hfactor hnonneg hpositive i =
      fiberWeight lambda tau rho p i :=
  rfl

/-- Membership in a fixed positive fiber, independent of proof packaging. -/
def MemFiber (lambda : Fin 4 → ℝ) (tau rho : ℝ)
    (p : MonicQuadratic) (x : Weights) : Prop :=
  ∀ i, x i = fiberWeight lambda tau rho p i

/-- The positive `p`-fiber, already intersected with the four-node simplex. -/
def positiveFiber (lambda : Fin 4 → ℝ) (tau rho : ℝ)
    (p : MonicQuadratic) : Set Weights :=
  {x | MemFiber lambda tau rho p x}

theorem memFiber_weight_mul_eval
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x) (i : Fin 4) :
    x i * p.toPolynomial.eval (lambda i) =
      tau ^ 2 * (lambda i - rho) / E lambda i := by
  have hE := E_ne_zero hlambda i
  have hp := (factor_eval_ne_zero htau hfactor i).1
  rw [hx i, fiberWeight]
  field_simp [hE, hp]

theorem memFiber_orthogonal_one
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x) :
    weightedPolyInner lambda x p.toPolynomial 1 = 0 := by
  rw [weightedPolyInner]
  simp only [eval_one, mul_one]
  calc
    ∑ i, x i * p.toPolynomial.eval (lambda i) =
        ∑ i, tau ^ 2 * (lambda i - rho) / E lambda i := by
      apply Finset.sum_congr rfl
      intro i _
      exact memFiber_weight_mul_eval hlambda htau hfactor hx i
    _ = tau ^ 2 * ∑ i, (lambda i - rho) / E lambda i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [sum_sub_div_E hlambda rho, mul_zero]

theorem memFiber_orthogonal_X
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x) :
    weightedPolyInner lambda x p.toPolynomial X = 0 := by
  rw [weightedPolyInner]
  simp only [eval_X]
  calc
    ∑ i, x i * p.toPolynomial.eval (lambda i) * lambda i =
        ∑ i, tau ^ 2 *
          (lambda i * (lambda i - rho) / E lambda i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [memFiber_weight_mul_eval hlambda htau hfactor hx i]
      ring
    _ = tau ^ 2 *
        ∑ i, lambda i * (lambda i - rho) / E lambda i := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [sum_lambda_mul_sub_div_E hlambda rho, mul_zero]

private theorem weightedPolyInner_monic_one_fiber
    (lambda : Fin 4 → ℝ) (x : Weights) (p : MonicQuadratic) :
    weightedPolyInner lambda x p.toPolynomial 1 =
      weightedMoment lambda x 2 +
        p.linearCoeff * weightedMoment lambda x 1 +
          p.constantCoeff * weightedMoment lambda x 0 := by
  simp only [weightedPolyInner, MonicQuadratic.eval, eval_one, mul_one,
    weightedMoment, pow_zero, pow_one]
  calc
    ∑ i, x i * (lambda i ^ 2 + p.linearCoeff * lambda i + p.constantCoeff) =
        ∑ i, (x i * lambda i ^ 2 +
          p.linearCoeff * (x i * lambda i) + p.constantCoeff * x i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, x i * lambda i ^ 2) +
        p.linearCoeff * (∑ i, x i * lambda i) +
          p.constantCoeff * (∑ i, x i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.mul_sum]

private theorem weightedPolyInner_monic_X_fiber
    (lambda : Fin 4 → ℝ) (x : Weights) (p : MonicQuadratic) :
    weightedPolyInner lambda x p.toPolynomial X =
      weightedMoment lambda x 3 +
        p.linearCoeff * weightedMoment lambda x 2 +
          p.constantCoeff * weightedMoment lambda x 1 := by
  simp only [weightedPolyInner, MonicQuadratic.eval, eval_X, weightedMoment,
    pow_one]
  calc
    ∑ i, x i * (lambda i ^ 2 + p.linearCoeff * lambda i + p.constantCoeff) *
        lambda i =
      ∑ i, (x i * lambda i ^ 3 +
        p.linearCoeff * (x i * lambda i ^ 2) +
          p.constantCoeff * (x i * lambda i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, x i * lambda i ^ 3) +
        p.linearCoeff * (∑ i, x i * lambda i ^ 2) +
          p.constantCoeff * (∑ i, x i * lambda i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.mul_sum]

/-- A monic quadratic satisfying the two weighted orthogonality equations is
the explicit Cramer-system polynomial `P_x`. -/
theorem eq_P_of_orthogonal
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (p : MonicQuadratic)
    (hone : weightedPolyInner lambda x p.toPolynomial 1 = 0)
    (hX : weightedPolyInner lambda x p.toPolynomial X = 0) :
    p = P lambda x := by
  rw [weightedPolyInner_monic_one_fiber] at hone
  rw [weightedPolyInner_monic_X_fiber] at hX
  have hdet := weightedMomentGramDet_ne_zero hlambda x
  apply MonicQuadratic.ext
  · change p.linearCoeff =
      (weightedMoment lambda x 1 * weightedMoment lambda x 2 -
        weightedMoment lambda x 0 * weightedMoment lambda x 3) /
          weightedMomentGramDet lambda x
    field_simp [hdet]
    rw [weightedMomentGramDet]
    linear_combination
      weightedMoment lambda x 0 * hX - weightedMoment lambda x 1 * hone
  · change p.constantCoeff =
      (weightedMoment lambda x 1 * weightedMoment lambda x 3 -
        weightedMoment lambda x 2 ^ 2) /
          weightedMomentGramDet lambda x
    field_simp [hdet]
    rw [weightedMomentGramDet]
    linear_combination
      weightedMoment lambda x 2 * hone - weightedMoment lambda x 1 * hX

/-- The candidate fiber has precisely the prescribed Arnoldi factor. -/
theorem P_eq_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x) :
    P lambda x = p := by
  symm
  exact eq_P_of_orthogonal hlambda x p
    (memFiber_orthogonal_one hlambda htau hfactor hx)
    (memFiber_orthogonal_X hlambda htau hfactor hx)

/-- The height on a limiting fiber is the common nodal product `tau²`. -/
theorem height_eq_tau_sq_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x) :
    H lambda x = tau ^ 2 := by
  change weightedPolyInner lambda x (P lambda x).toPolynomial
    (P lambda x).toPolynomial = tau ^ 2
  rw [weightedPolyInner, P_eq_of_memFiber hlambda htau hfactor hx]
  calc
    ∑ i, x i * p.toPolynomial.eval (lambda i) *
        p.toPolynomial.eval (lambda i) =
      ∑ i, (tau ^ 2 * (lambda i - rho) / E lambda i) *
        p.toPolynomial.eval (lambda i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [memFiber_weight_mul_eval hlambda htau hfactor hx i]
    _ = tau ^ 2 *
        ∑ i, (lambda i - rho) * p.toPolynomial.eval (lambda i) /
          E lambda i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = tau ^ 2 := by
      rw [sum_sub_mul_monicQuadratic_eval_div_E hlambda rho p, mul_one]

/-- The rational parameter used to define a limiting fiber agrees with the
intrinsic four-node parameter of every point on that fiber. -/
theorem rho_eq_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho₀ p x) :
    rho lambda x = rho₀ := by
  have hP := P_eq_of_memFiber hlambda htau hfactor hx
  have hH := height_eq_tau_sq_of_memFiber hlambda htau hfactor hx
  have hnode := memFiber_weight_mul_eval hlambda htau hfactor hx (0 : Fin 4)
  have hE := E_ne_zero hlambda (0 : Fin 4)
  have htauSq : tau ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt htau)
  calc
    rho lambda x = lambda 0 -
        E lambda 0 *
          (x 0 * (P lambda x).toPolynomial.eval (lambda 0)) /
            H lambda x := rho_eq_node_formula hlambda x 0
    _ = rho₀ := by
      rw [hP, hH, hnode]
      field_simp [hE, htauSq]
      ring

/-- One four-node update sends the `p`-fiber to the companion `q`-fiber. -/
theorem T_weight_eq_companion_fiberWeight
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho₀ p x) (i : Fin 4) :
    T lambda hlambda x i = fiberWeight lambda tau rho₀ q i := by
  have hfactor' : q.toPolynomial * p.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2) := by
    simpa [mul_comm] using hfactor
  have hP := P_eq_of_memFiber hlambda htau hfactor hx
  have hH := height_eq_tau_sq_of_memFiber hlambda htau hfactor hx
  rw [T_weight, hP, hH, hx i]
  rw [fiberWeight_eq_otherFactor hlambda htau hfactor i,
    fiberWeight_eq_otherFactor hlambda htau hfactor' i]
  have hE := E_ne_zero hlambda i
  have htauSq : tau ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt htau)
  have hnode := factor_eval_mul_eq_tau_sq hfactor i
  field_simp [hE, htauSq]
  rw [← hnode]
  ring

theorem memFiber_T
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho₀ p x) :
    MemFiber lambda tau rho₀ q (T lambda hlambda x) :=
  T_weight_eq_companion_fiberWeight hlambda htau hfactor hx

theorem P_T_eq_companion_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho₀ p x) :
    P lambda (T lambda hlambda x) = q := by
  have hfactor' : q.toPolynomial * p.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2) := by
    simpa [mul_comm] using hfactor
  exact P_eq_of_memFiber hlambda htau hfactor'
    (memFiber_T hlambda htau hfactor hx)

theorem height_T_eq_tau_sq_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho₀ p x) :
    H lambda (T lambda hlambda x) = tau ^ 2 := by
  have hfactor' : q.toPolynomial * p.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2) := by
    simpa [mul_comm] using hfactor
  exact height_eq_tau_sq_of_memFiber hlambda htau hfactor'
    (memFiber_T hlambda htau hfactor hx)

theorem rho_T_eq_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho₀ p x) :
    rho lambda (T lambda hlambda x) = rho₀ := by
  have hfactor' : q.toPolynomial * p.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2) := by
    simpa [mul_comm] using hfactor
  exact rho_eq_of_memFiber hlambda htau hfactor'
    (memFiber_T hlambda htau hfactor hx)

theorem rho_T_eq_rho_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho₀ p x) :
    rho lambda (T lambda hlambda x) = rho lambda x := by
  rw [rho_T_eq_of_memFiber hlambda htau hfactor hx,
    rho_eq_of_memFiber hlambda htau hfactor hx]

private theorem weights_eq_of_apply_eq {x y : Weights}
    (h : ∀ i, x i = y i) : x = y := by
  cases x with
  | mk xWeight xNonneg xSum xCard =>
      cases y with
      | mk yWeight yNonneg ySum yCard =>
          have hWeight : xWeight = yWeight := funext h
          subst yWeight
          rfl

/-- The limiting four-node map is exactly two-periodic on every positive
fiber, including its three-positive boundary point. -/
theorem T_T_eq_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho₀ p x) :
    T lambda hlambda (T lambda hlambda x) = x := by
  have hfactor' : q.toPolynomial * p.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2) := by
    simpa [mul_comm] using hfactor
  have hback : MemFiber lambda tau rho₀ p
      (T lambda hlambda (T lambda hlambda x)) :=
    memFiber_T hlambda htau hfactor'
      (memFiber_T hlambda htau hfactor hx)
  apply weights_eq_of_apply_eq
  intro i
  exact (hback i).trans (hx i).symm

/-- Set-level form of the exact companion-fiber interchange. -/
theorem image_T_positiveFiber
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) :
    T lambda hlambda '' positiveFiber lambda tau rho₀ p =
      positiveFiber lambda tau rho₀ q := by
  have hfactor' : q.toPolynomial * p.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2) := by
    simpa [mul_comm] using hfactor
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact memFiber_T hlambda htau hfactor hx
  · intro y hy
    refine ⟨T lambda hlambda y,
      memFiber_T hlambda htau hfactor' hy, ?_⟩
    exact T_T_eq_of_memFiber hlambda htau hfactor' hy

/-- A fixed fiber contains at most one simplex point; the apparent fiber
parameterization is therefore canonical after `tau`, `rho`, and the factor
are fixed. -/
theorem positiveFiber_subsingleton
    (lambda : Fin 4 → ℝ) (tau rho₀ : ℝ) (p : MonicQuadratic) :
    (positiveFiber lambda tau rho₀ p).Subsingleton := by
  intro x hx y hy
  apply weights_eq_of_apply_eq
  intro i
  exact (hx i).trans (hy i).symm

/-- A boundary fiber can lose at most one active node; if two fiber weights
vanish, their indices coincide. -/
theorem memFiber_zero_index_unique
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    {tau : ℝ} (htau : 0 < tau) {rho₀ : ℝ} {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho₀ p x)
    {i j : Fin 4} (hi : x i = 0) (hj : x j = 0) : i = j := by
  apply hlambda
  have hi' : fiberWeight lambda tau rho₀ p i = 0 := by
    rw [← hx i]
    exact hi
  have hj' : fiberWeight lambda tau rho₀ p j = 0 := by
    rw [← hx j]
    exact hj
  rw [fiberWeight_eq_zero_iff hlambda htau hfactor i] at hi'
  rw [fiberWeight_eq_zero_iff hlambda htau hfactor j] at hj'
  exact hi'.trans hj'.symm

theorem memFiber_fiberPoint
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (tau : ℝ) (htau : 0 < tau) (rho₀ : ℝ) (p q : MonicQuadratic)
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hnonneg : ∀ i, 0 ≤ fiberWeight lambda tau rho₀ p i)
    (hpositive : 3 ≤
      (Finset.univ.filter fun i ↦
        0 < fiberWeight lambda tau rho₀ p i).card) :
    MemFiber lambda tau rho₀ p
      (fiberPoint lambda hlambda tau htau rho₀ p q hfactor hnonneg hpositive) := by
  intro i
  rfl

theorem P_fiberPoint
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (tau : ℝ) (htau : 0 < tau) (rho₀ : ℝ) (p q : MonicQuadratic)
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hnonneg : ∀ i, 0 ≤ fiberWeight lambda tau rho₀ p i)
    (hpositive : 3 ≤
      (Finset.univ.filter fun i ↦
        0 < fiberWeight lambda tau rho₀ p i).card) :
    P lambda
      (fiberPoint lambda hlambda tau htau rho₀ p q hfactor hnonneg hpositive) = p :=
  P_eq_of_memFiber hlambda htau hfactor
    (memFiber_fiberPoint lambda hlambda tau htau rho₀ p q hfactor
      hnonneg hpositive)

theorem height_fiberPoint
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (tau : ℝ) (htau : 0 < tau) (rho₀ : ℝ) (p q : MonicQuadratic)
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hnonneg : ∀ i, 0 ≤ fiberWeight lambda tau rho₀ p i)
    (hpositive : 3 ≤
      (Finset.univ.filter fun i ↦
        0 < fiberWeight lambda tau rho₀ p i).card) :
    H lambda
      (fiberPoint lambda hlambda tau htau rho₀ p q hfactor hnonneg hpositive) =
        tau ^ 2 :=
  height_eq_tau_sq_of_memFiber hlambda htau hfactor
    (memFiber_fiberPoint lambda hlambda tau htau rho₀ p q hfactor
      hnonneg hpositive)

/-- Once the rational weights satisfy the simplex hypotheses, the positive
fiber is literally the singleton containing their packaged point. -/
theorem positiveFiber_eq_singleton_fiberPoint
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (tau : ℝ) (htau : 0 < tau) (rho₀ : ℝ) (p q : MonicQuadratic)
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hnonneg : ∀ i, 0 ≤ fiberWeight lambda tau rho₀ p i)
    (hpositive : 3 ≤
      (Finset.univ.filter fun i ↦
        0 < fiberWeight lambda tau rho₀ p i).card) :
    positiveFiber lambda tau rho₀ p =
      {fiberPoint lambda hlambda tau htau rho₀ p q hfactor hnonneg hpositive} := by
  let x₀ := fiberPoint lambda hlambda tau htau rho₀ p q hfactor
    hnonneg hpositive
  have hx₀ : MemFiber lambda tau rho₀ p x₀ :=
    memFiber_fiberPoint lambda hlambda tau htau rho₀ p q hfactor
      hnonneg hpositive
  ext x
  constructor
  · intro hx
    change MemFiber lambda tau rho₀ p x at hx
    change x ∈ ({x₀} : Set Weights)
    rw [Set.mem_singleton_iff]
    apply weights_eq_of_apply_eq
    intro i
    exact (hx i).trans (hx₀ i).symm
  · intro hx
    change x ∈ ({x₀} : Set Weights) at hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hx₀

/-- The same fiber as a closed set of ambient weight coordinates.  Simplex
packaging is supplied separately by `fiberPoint`. -/
def closedFiberCoordinates (lambda : Fin 4 → ℝ) (tau rho₀ : ℝ)
    (p : MonicQuadratic) : Set (Fin 4 → ℝ) :=
  {fiberWeight lambda tau rho₀ p}

theorem isClosed_closedFiberCoordinates
    (lambda : Fin 4 → ℝ) (tau rho₀ : ℝ) (p : MonicQuadratic) :
    IsClosed (closedFiberCoordinates lambda tau rho₀ p) :=
  isClosed_singleton

/-- The ambient-coordinate fiber curve obtained by allowing `rho` to range
over a parameter set. -/
def fiberCurveCoordinates (lambda : Fin 4 → ℝ) (tau : ℝ)
    (p : MonicQuadratic) (J : Set ℝ) : Set (Fin 4 → ℝ) :=
  (fun rho₀ ↦ fiberWeight lambda tau rho₀ p) '' J

theorem continuous_fiberWeight_parameter
    (lambda : Fin 4 → ℝ) (tau : ℝ) (p : MonicQuadratic) :
    Continuous (fun rho₀ ↦ fiberWeight lambda tau rho₀ p) := by
  unfold fiberWeight
  fun_prop

theorem isCompact_fiberCurveCoordinates
    (lambda : Fin 4 → ℝ) (tau : ℝ) (p : MonicQuadratic)
    {J : Set ℝ} (hJ : IsCompact J) :
    IsCompact (fiberCurveCoordinates lambda tau p J) := by
  exact hJ.image (continuous_fiberWeight_parameter lambda tau p)

/-- A compact parameter interval gives the closed positive-fiber curve used
in the four-node closure argument. -/
theorem isClosed_fiberCurveCoordinates
    (lambda : Fin 4 → ℝ) (tau : ℝ) (p : MonicQuadratic)
    {J : Set ℝ} (hJ : IsCompact J) :
    IsClosed (fiberCurveCoordinates lambda tau p J) :=
  (isCompact_fiberCurveCoordinates lambda tau p hJ).isClosed

/-- Compactness turns pointwise nonvanishing of the factor product on a
closed node gap into the uniform manuscript gap estimate. -/
theorem exists_uniform_factor_product_gap_on_compact
    (p q : MonicQuadratic) {J : Set ℝ} (hJ : IsCompact J)
    (hnonzero : ∀ rho₀ ∈ J,
      p.toPolynomial.eval rho₀ * q.toPolynomial.eval rho₀ ≠ 0) :
    ∃ delta, 0 < delta ∧ ∀ rho₀ ∈ J,
      delta ≤
        |p.toPolynomial.eval rho₀ * q.toPolynomial.eval rho₀| := by
  apply hJ.exists_forall_le'
  · exact (p.toPolynomial.continuous.mul
      q.toPolynomial.continuous).abs.continuousOn
  · intro rho₀ hrho
    exact abs_pos.mpr (hnonzero rho₀ hrho)

/-- The limiting factors are uniformly separated from zero on the four
active nodes.  This is the finite-node nonvanishing gap used for compact
fiber estimates. -/
theorem exists_common_node_factor_gap
    {lambda : Fin 4 → ℝ} {tau : ℝ} (htau : 0 < tau)
    {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2)) :
    ∃ delta, 0 < delta ∧ ∀ i,
      delta ≤ |p.toPolynomial.eval (lambda i)| ∧
      delta ≤ |q.toPolynomial.eval (lambda i)| := by
  obtain ⟨ip, -, hpmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin 4))
    (fun i ↦ |p.toPolynomial.eval (lambda i)|) Finset.univ_nonempty
  obtain ⟨iq, -, hqmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin 4))
    (fun i ↦ |q.toPolynomial.eval (lambda i)|) Finset.univ_nonempty
  have hpip : 0 < |p.toPolynomial.eval (lambda ip)| :=
    abs_pos.mpr (factor_eval_ne_zero htau hfactor ip).1
  have hqiq : 0 < |q.toPolynomial.eval (lambda iq)| :=
    abs_pos.mpr (factor_eval_ne_zero htau hfactor iq).2
  refine ⟨min |p.toPolynomial.eval (lambda ip)|
      |q.toPolynomial.eval (lambda iq)|, lt_min hpip hqiq, ?_⟩
  intro i
  constructor
  · exact (min_le_left _ _).trans (hpmin i (Finset.mem_univ i))
  · exact (min_le_right _ _).trans (hqmin i (Finset.mem_univ i))

end

end FourNode
end Forsythe
