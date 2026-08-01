import Forsythe.FourNode.Fiber
import Mathlib.Topology.Order.IntermediateValue

/-!
# The central four-node gap

For ordered nodes and positive height, an admissible limiting four-node fiber
has its barycentric parameter in the middle node gap.  The short proof stays
in weighted-orthogonality coordinates: a parameter outside that gap
would force opposite signs of the limiting quadratic at the two middle nodes,
and hence a root where `Pi + tau²` is strictly positive.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Polynomial Set

noncomputable section

private theorem erase_one_fin_four_gap :
    (Finset.univ.erase (1 : Fin 4)) = {0, 2, 3} := by decide

private theorem erase_two_fin_four_gap :
    (Finset.univ.erase (2 : Fin 4)) = {0, 1, 3} := by decide

/-- The first middle barycentric denominator is positive for ordered nodes. -/
theorem E_one_pos_of_strictMono
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda) :
    0 < E lambda 1 := by
  have h01 : lambda 0 < lambda 1 := hlambda (by decide)
  have h12 : lambda 1 < lambda 2 := hlambda (by decide)
  have h13 : lambda 1 < lambda 3 := hlambda (by decide)
  rw [E, cubicLagrangeDenominator, erase_one_fin_four_gap]
  simp
  exact mul_pos (sub_pos.mpr h01)
    (mul_pos_of_neg_of_neg (sub_neg.mpr h12) (sub_neg.mpr h13))

/-- The second middle barycentric denominator is negative for ordered nodes. -/
theorem E_two_neg_of_strictMono
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda) :
    E lambda 2 < 0 := by
  have h02 : lambda 0 < lambda 2 := hlambda (by decide)
  have h12 : lambda 1 < lambda 2 := hlambda (by decide)
  have h23 : lambda 2 < lambda 3 := hlambda (by decide)
  rw [E, cubicLagrangeDenominator, erase_two_fin_four_gap]
  simp
  exact mul_neg_of_pos_of_neg (sub_pos.mpr h02)
    (mul_neg_of_pos_of_neg (sub_pos.mpr h12) (sub_neg.mpr h23))

/-- The nodal quartic is nonnegative on the closed middle node gap. -/
theorem nodalQuartic_eval_nonneg_on_middleGap
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {t : ℝ} (ht : t ∈ Icc (lambda 1) (lambda 2)) :
    0 ≤ (nodalQuartic lambda).eval t := by
  have h01 : lambda 0 < lambda 1 := hlambda (by decide)
  have h23 : lambda 2 < lambda 3 := hlambda (by decide)
  have h0 : 0 ≤ t - lambda 0 := by linarith [ht.1]
  have h1 : 0 ≤ t - lambda 1 := sub_nonneg.mpr ht.1
  have h2 : 0 ≤ lambda 2 - t := sub_nonneg.mpr ht.2
  have h3 : 0 ≤ lambda 3 - t := by linarith [ht.2]
  rw [nodalQuartic, eval_prod, Fin.prod_univ_four]
  simp only [eval_sub, eval_X, eval_C]
  rw [show
      (t - lambda 0) * (t - lambda 1) *
          (t - lambda 2) * (t - lambda 3) =
        ((t - lambda 0) * (t - lambda 1)) *
          ((lambda 2 - t) * (lambda 3 - t)) by ring]
  exact mul_nonneg (mul_nonneg h0 h1) (mul_nonneg h2 h3)

/-- The nodal quartic is strictly positive in the open middle node gap. -/
theorem nodalQuartic_eval_pos_on_middleGap
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {t : ℝ} (ht : t ∈ Ioo (lambda 1) (lambda 2)) :
    0 < (nodalQuartic lambda).eval t := by
  have h01 : lambda 0 < lambda 1 := hlambda (by decide)
  have h23 : lambda 2 < lambda 3 := hlambda (by decide)
  have h0 : 0 < t - lambda 0 := by linarith [ht.1]
  have h1 : 0 < t - lambda 1 := sub_pos.mpr ht.1
  have h2 : 0 < lambda 2 - t := sub_pos.mpr ht.2
  have h3 : 0 < lambda 3 - t := by linarith [ht.2]
  rw [nodalQuartic, eval_prod, Fin.prod_univ_four]
  simp only [eval_sub, eval_X, eval_C]
  rw [show
      (t - lambda 0) * (t - lambda 1) *
          (t - lambda 2) * (t - lambda 3) =
        ((t - lambda 0) * (t - lambda 1)) *
          ((lambda 2 - t) * (lambda 3 - t)) by ring]
  exact mul_pos (mul_pos h0 h1) (mul_pos h2 h3)

/-- Neither limiting quadratic vanishes on the closed middle node gap. -/
theorem factor_eval_ne_zero_on_middleGap
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {t : ℝ} (ht : t ∈ Icc (lambda 1) (lambda 2)) :
    p.toPolynomial.eval t ≠ 0 ∧ q.toPolynomial.eval t ≠ 0 := by
  have hPi := nodalQuartic_eval_nonneg_on_middleGap hlambda ht
  have htauSq : 0 < tau ^ 2 := sq_pos_of_pos htau
  have heval := congrArg (Polynomial.eval t) hfactor
  simp only [eval_mul, eval_add, eval_C] at heval
  constructor
  · intro hp
    rw [hp, zero_mul] at heval
    linarith
  · intro hq
    rw [hq, mul_zero] at heval
    linarith

private theorem exists_factor_root_between_middle
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    (p : MonicQuadratic)
    (hforward :
      (0 < p.toPolynomial.eval (lambda 1) ∧
        p.toPolynomial.eval (lambda 2) < 0) ∨
      (p.toPolynomial.eval (lambda 1) < 0 ∧
        0 < p.toPolynomial.eval (lambda 2))) :
    ∃ t ∈ Icc (lambda 1) (lambda 2), p.toPolynomial.eval t = 0 := by
  have h12 : lambda 1 ≤ lambda 2 := (hlambda (by decide)).le
  rcases hforward with hdown | hup
  · have hzero : (0 : ℝ) ∈ Icc
        (p.toPolynomial.eval (lambda 2))
        (p.toPolynomial.eval (lambda 1)) := ⟨hdown.2.le, hdown.1.le⟩
    simpa only [Set.mem_image] using
      (intermediate_value_Icc' h12 p.toPolynomial.continuous.continuousOn hzero)
  · have hzero : (0 : ℝ) ∈ Icc
        (p.toPolynomial.eval (lambda 1))
        (p.toPolynomial.eval (lambda 2)) := ⟨hup.1.le, hup.2.le⟩
    simpa only [Set.mem_image] using
      (intermediate_value_Icc h12 p.toPolynomial.continuous.continuousOn hzero)

/-- Every admissible limiting fiber parameter lies in the closed middle gap. -/
theorem rho_mem_middleGap_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ}
    {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x) :
    rho ∈ Icc (lambda 1) (lambda 2) := by
  have hE1 := E_one_pos_of_strictMono hlambda
  have hE2 := E_two_neg_of_strictMono hlambda
  have htauSq : 0 < tau ^ 2 := sq_pos_of_pos htau
  constructor
  · by_contra hnot
    have hrho : rho < lambda 1 := lt_of_not_ge hnot
    have h12 : lambda 1 < lambda 2 := hlambda (by decide)
    have hprod1 : 0 < x 1 * p.toPolynomial.eval (lambda 1) := by
      rw [memFiber_weight_mul_eval hlambda.injective htau hfactor hx]
      exact div_pos (mul_pos htauSq (sub_pos.mpr hrho)) hE1
    have hp1 : 0 < p.toPolynomial.eval (lambda 1) := by
      rcases (mul_pos_iff.mp hprod1) with h | h
      · exact h.2
      · exact (not_lt_of_ge (x.nonneg 1) h.1).elim
    have hprod2 : x 2 * p.toPolynomial.eval (lambda 2) < 0 := by
      rw [memFiber_weight_mul_eval hlambda.injective htau hfactor hx]
      exact div_neg_of_pos_of_neg
        (mul_pos htauSq (sub_pos.mpr (hrho.trans h12))) hE2
    have hp2 : p.toPolynomial.eval (lambda 2) < 0 := by
      rcases (mul_neg_iff.mp hprod2) with h | h
      · exact h.2
      · exact (not_lt_of_ge (x.nonneg 2) h.1).elim
    obtain ⟨t, ht, hroot⟩ :=
      exists_factor_root_between_middle hlambda p (Or.inl ⟨hp1, hp2⟩)
    exact (factor_eval_ne_zero_on_middleGap hlambda htau hfactor ht).1 hroot
  · by_contra hnot
    have hrho : lambda 2 < rho := lt_of_not_ge hnot
    have h12 : lambda 1 < lambda 2 := hlambda (by decide)
    have hprod1 : x 1 * p.toPolynomial.eval (lambda 1) < 0 := by
      rw [memFiber_weight_mul_eval hlambda.injective htau hfactor hx]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg htauSq (sub_neg.mpr (h12.trans hrho))) hE1
    have hp1 : p.toPolynomial.eval (lambda 1) < 0 := by
      rcases (mul_neg_iff.mp hprod1) with h | h
      · exact h.2
      · exact (not_lt_of_ge (x.nonneg 1) h.1).elim
    have hprod2 : 0 < x 2 * p.toPolynomial.eval (lambda 2) := by
      rw [memFiber_weight_mul_eval hlambda.injective htau hfactor hx]
      exact div_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg htauSq (sub_neg.mpr hrho)) hE2
    have hp2 : 0 < p.toPolynomial.eval (lambda 2) := by
      rcases (mul_pos_iff.mp hprod2) with h | h
      · exact h.2
      · exact (not_lt_of_ge (x.nonneg 2) h.1).elim
    obtain ⟨t, ht, hroot⟩ :=
      exists_factor_root_between_middle hlambda p (Or.inr ⟨hp1, hp2⟩)
    exact (factor_eval_ne_zero_on_middleGap hlambda htau hfactor ht).1 hroot

/-- An interior (four-positive) fiber has parameter strictly between the two
middle nodes. -/
theorem rho_mem_open_middleGap_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ}
    {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x)
    (hpositive : ∀ i, 0 < x i) :
    rho ∈ Ioo (lambda 1) (lambda 2) := by
  have hclosed := rho_mem_middleGap_of_memFiber hlambda htau hfactor hx
  refine ⟨lt_of_le_of_ne hclosed.1 ?_, lt_of_le_of_ne hclosed.2 ?_⟩
  · intro heq
    have hzero : fiberWeight lambda tau rho p 1 = 0 :=
      (fiberWeight_eq_zero_iff hlambda.injective htau hfactor 1).2 heq
    rw [← hx 1] at hzero
    exact (ne_of_gt (hpositive 1)) hzero
  · intro heq
    have hzero : fiberWeight lambda tau rho p 2 = 0 :=
      (fiberWeight_eq_zero_iff hlambda.injective htau hfactor 2).2 heq.symm
    rw [← hx 2] at hzero
    exact (ne_of_gt (hpositive 2)) hzero

/-- At an interior limiting fiber, both limiting factors are negative at the
two middle nodes.  This sign pattern later confines every sufficiently close
principal-weight state to the same gap. -/
theorem factor_eval_middle_nodes_neg_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {rho : ℝ}
    {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x)
    (hpositive : ∀ i, 0 < x i) :
    p.toPolynomial.eval (lambda 1) < 0 ∧
      p.toPolynomial.eval (lambda 2) < 0 ∧
      q.toPolynomial.eval (lambda 1) < 0 ∧
      q.toPolynomial.eval (lambda 2) < 0 := by
  have hrho := rho_mem_open_middleGap_of_memFiber
    hlambda htau hfactor hx hpositive
  have hE1 := E_one_pos_of_strictMono hlambda
  have hE2 := E_two_neg_of_strictMono hlambda
  have htauSq : 0 < tau ^ 2 := sq_pos_of_pos htau
  have hprod1 : x 1 * p.toPolynomial.eval (lambda 1) < 0 := by
    rw [memFiber_weight_mul_eval hlambda.injective htau hfactor hx]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg htauSq (sub_neg.mpr hrho.1)) hE1
  have hp1 : p.toPolynomial.eval (lambda 1) < 0 :=
    ((mul_neg_iff.mp hprod1).resolve_right fun h ↦
      (not_lt_of_ge (x.nonneg 1)) h.1).2
  have hprod2 : x 2 * p.toPolynomial.eval (lambda 2) < 0 := by
    rw [memFiber_weight_mul_eval hlambda.injective htau hfactor hx]
    exact div_neg_of_pos_of_neg
      (mul_pos htauSq (sub_pos.mpr hrho.2)) hE2
  have hp2 : p.toPolynomial.eval (lambda 2) < 0 :=
    ((mul_neg_iff.mp hprod2).resolve_right fun h ↦
      (not_lt_of_ge (x.nonneg 2)) h.1).2
  have hq1 : q.toPolynomial.eval (lambda 1) < 0 := by
    rcases factor_eval_same_sign htau hfactor 1 with h | h
    · exact (not_lt_of_ge h.1.le hp1).elim
    · exact h.2
  have hq2 : q.toPolynomial.eval (lambda 2) < 0 := by
    rcases factor_eval_same_sign htau hfactor 2 with h | h
    · exact (not_lt_of_ge h.1.le hp2).elim
    · exact h.2
  exact ⟨hp1, hp2, hq1, hq2⟩

/-- Negative factor values at the two middle nodes force an arbitrary
four-positive state into the open middle gap. -/
theorem rho_mem_open_middleGap_of_P_eval_neg
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    (x : Weights) (hpositive : ∀ i, 0 < x i)
    (hP1 : (P lambda x).toPolynomial.eval (lambda 1) < 0)
    (hP2 : (P lambda x).toPolynomial.eval (lambda 2) < 0) :
    rho lambda x ∈ Ioo (lambda 1) (lambda 2) := by
  have hH : 0 < H lambda x := height_pos hlambda.injective x
  have hE1 := E_one_pos_of_strictMono hlambda
  have hE2 := E_two_neg_of_strictMono hlambda
  have hone := weight_mul_P_eval_eq_height_mul_sub_rho_div_E
    hlambda.injective x 1
  have htwo := weight_mul_P_eval_eq_height_mul_sub_rho_div_E
    hlambda.injective x 2
  have hone' := (eq_div_iff (ne_of_gt hE1)).mp hone
  have htwo' := (eq_div_iff (ne_of_lt hE2)).mp htwo
  have hleftProduct :
      x 1 * (P lambda x).toPolynomial.eval (lambda 1) * E lambda 1 < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (hpositive 1) hP1) hE1
  have hrightProduct :
      0 < x 2 * (P lambda x).toPolynomial.eval (lambda 2) * E lambda 2 :=
    mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (hpositive 2) hP2) hE2
  constructor <;> nlinarith

end

end FourNode
end Forsythe
