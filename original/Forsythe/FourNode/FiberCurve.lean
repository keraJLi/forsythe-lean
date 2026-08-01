import Forsythe.FourNode.Continuity
import Forsythe.FourNode.Gap
import Mathlib.Algebra.Polynomial.Div

/-!
# Admissible four-node fiber curves

This module packages the limiting fiber parameterization in the four-node
simplex itself.  For an ordered node set, the endpoint sign pattern of the
two limiting factors makes the barycentric formulas nonnegative throughout
the closed middle gap; the two exterior weights are always positive, and at
least one middle weight is positive.  Thus every parameter gives a genuine
`Weights` state, including the two three-positive boundary states.

The same sign pattern also places the two roots of each limiting quadratic:
one lies in the first node gap and the other in the last node gap.  The proof
uses the intermediate value theorem and monicity to record the resulting
exact linear-factor decomposition.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Polynomial Set

noncomputable section

private theorem erase_zero_fin_four_fiberCurve :
    (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} := by decide

private theorem erase_three_fin_four_fiberCurve :
    (Finset.univ.erase (3 : Fin 4)) = {0, 1, 2} := by decide

/-- The left exterior barycentric denominator is negative for ordered nodes. -/
theorem E_zero_neg_of_strictMono
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda) :
    E lambda 0 < 0 := by
  have h01 : lambda 0 < lambda 1 := hlambda (by decide)
  have h02 : lambda 0 < lambda 2 := hlambda (by decide)
  have h03 : lambda 0 < lambda 3 := hlambda (by decide)
  rw [E, cubicLagrangeDenominator, erase_zero_fin_four_fiberCurve]
  simp
  exact mul_neg_of_neg_of_pos (sub_neg.mpr h01)
    (mul_pos_of_neg_of_neg (sub_neg.mpr h02) (sub_neg.mpr h03))

/-- The right exterior barycentric denominator is positive for ordered nodes. -/
theorem E_three_pos_of_strictMono
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda) :
    0 < E lambda 3 := by
  have h03 : lambda 0 < lambda 3 := hlambda (by decide)
  have h13 : lambda 1 < lambda 3 := hlambda (by decide)
  have h23 : lambda 2 < lambda 3 := hlambda (by decide)
  rw [E, cubicLagrangeDenominator, erase_three_fin_four_fiberCurve]
  simp
  exact mul_pos (sub_pos.mpr h03)
    (mul_pos (sub_pos.mpr h13) (sub_pos.mpr h23))

/-- The endpoint sign pattern that characterizes an admissible limiting
quadratic: positive at the two exterior nodes and negative at the two middle
nodes. -/
structure OuterGapSignPattern (lambda : Fin 4 → ℝ)
    (r : MonicQuadratic) : Prop where
  at_zero_pos : 0 < r.toPolynomial.eval (lambda 0)
  at_one_neg : r.toPolynomial.eval (lambda 1) < 0
  at_two_neg : r.toPolynomial.eval (lambda 2) < 0
  at_three_pos : 0 < r.toPolynomial.eval (lambda 3)

/-- A positive-height factorization whose two monic factors have the
admissible outer-gap sign pattern.  These are exactly the hypotheses needed
to parameterize both closed positive fibers without leaving the simplex. -/
structure AdmissibleFiberFactors (lambda : Fin 4 → ℝ) (tau : ℝ)
    (p q : MonicQuadratic) : Prop where
  tau_pos : 0 < tau
  factorization :
    p.toPolynomial * q.toPolynomial = nodalQuartic lambda + C (tau ^ 2)
  p_signs : OuterGapSignPattern lambda p
  q_signs : OuterGapSignPattern lambda q

/-- Interchanging the two limiting factors preserves admissibility. -/
theorem AdmissibleFiberFactors.swap
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q) :
    AdmissibleFiberFactors lambda tau q p where
  tau_pos := h.tau_pos
  factorization := by simpa [mul_comm] using h.factorization
  p_signs := h.q_signs
  q_signs := h.p_signs

/-- A four-positive point of a limiting fiber supplies the full endpoint
sign pattern for both factors. -/
theorem admissibleFiberFactors_of_memFiber
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau rho : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    {x : Weights} (hx : MemFiber lambda tau rho p x)
    (hpositive : ∀ i, 0 < x i) :
    AdmissibleFiberFactors lambda tau p q := by
  have hrho := rho_mem_open_middleGap_of_memFiber
    hlambda htau hfactor hx hpositive
  have hmiddle := factor_eval_middle_nodes_neg_of_memFiber
    hlambda htau hfactor hx hpositive
  have htauSq : 0 < tau ^ 2 := sq_pos_of_pos htau
  have hp0Product :
      0 < x 0 * p.toPolynomial.eval (lambda 0) := by
    rw [memFiber_weight_mul_eval hlambda.injective htau hfactor hx]
    exact div_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg htauSq
        (sub_neg.mpr ((hlambda (by decide)).trans hrho.1)))
      (E_zero_neg_of_strictMono hlambda)
  have hp0 : 0 < p.toPolynomial.eval (lambda 0) := by
    rcases (mul_pos_iff.mp hp0Product) with h | h
    · exact h.2
    · exact (not_lt_of_ge (x.nonneg 0) h.1).elim
  have hp3Product :
      0 < x 3 * p.toPolynomial.eval (lambda 3) := by
    rw [memFiber_weight_mul_eval hlambda.injective htau hfactor hx]
    exact div_pos
      (mul_pos htauSq
        (sub_pos.mpr (hrho.2.trans (hlambda (by decide)))))
      (E_three_pos_of_strictMono hlambda)
  have hp3 : 0 < p.toPolynomial.eval (lambda 3) := by
    rcases (mul_pos_iff.mp hp3Product) with h | h
    · exact h.2
    · exact (not_lt_of_ge (x.nonneg 3) h.1).elim
  have hq0 : 0 < q.toPolynomial.eval (lambda 0) := by
    rcases factor_eval_same_sign htau hfactor 0 with h | h
    · exact h.2
    · exact (not_lt_of_ge hp0.le h.1).elim
  have hq3 : 0 < q.toPolynomial.eval (lambda 3) := by
    rcases factor_eval_same_sign htau hfactor 3 with h | h
    · exact h.2
    · exact (not_lt_of_ge hp3.le h.1).elim
  exact
    { tau_pos := htau
      factorization := hfactor
      p_signs := ⟨hp0, hmiddle.1, hmiddle.2.1, hp3⟩
      q_signs := ⟨hq0, hmiddle.2.2.1, hmiddle.2.2.2, hq3⟩ }

theorem fiberWeight_zero_pos_on_middleGap
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hq : OuterGapSignPattern lambda q)
    (rho : Icc (lambda 1) (lambda 2)) :
    0 < fiberWeight lambda tau (rho : ℝ) p 0 := by
  rw [fiberWeight_eq_otherFactor hlambda.injective htau hfactor]
  exact div_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos
      (sub_neg.mpr ((hlambda (by decide)).trans_le rho.property.1))
      hq.at_zero_pos)
    (E_zero_neg_of_strictMono hlambda)

theorem fiberWeight_three_pos_on_middleGap
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hq : OuterGapSignPattern lambda q)
    (rho : Icc (lambda 1) (lambda 2)) :
    0 < fiberWeight lambda tau (rho : ℝ) p 3 := by
  rw [fiberWeight_eq_otherFactor hlambda.injective htau hfactor]
  exact div_pos
    (mul_pos
      (sub_pos.mpr (rho.property.2.trans_lt (hlambda (by decide))))
      hq.at_three_pos)
    (E_three_pos_of_strictMono hlambda)

theorem fiberWeight_one_pos_of_left_lt
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hq : OuterGapSignPattern lambda q) {rho : ℝ}
    (hrho : lambda 1 < rho) :
    0 < fiberWeight lambda tau rho p 1 := by
  rw [fiberWeight_eq_otherFactor hlambda.injective htau hfactor]
  exact div_pos
    (mul_pos_of_neg_of_neg (sub_neg.mpr hrho) hq.at_one_neg)
    (E_one_pos_of_strictMono hlambda)

theorem fiberWeight_two_pos_of_lt_right
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hq : OuterGapSignPattern lambda q) {rho : ℝ}
    (hrho : rho < lambda 2) :
    0 < fiberWeight lambda tau rho p 2 := by
  rw [fiberWeight_eq_otherFactor hlambda.injective htau hfactor]
  exact div_pos_of_neg_of_neg
    (mul_neg_of_pos_of_neg (sub_pos.mpr hrho) hq.at_two_neg)
    (E_two_neg_of_strictMono hlambda)

/-- On the closed middle gap, the rational `p`-fiber formula is pointwise
nonnegative whenever its companion factor has the admissible sign pattern. -/
theorem fiberWeight_nonneg_on_middleGap
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hq : OuterGapSignPattern lambda q)
    (rho : Icc (lambda 1) (lambda 2)) :
    ∀ i, 0 ≤ fiberWeight lambda tau (rho : ℝ) p i := by
  intro i
  fin_cases i
  · exact (fiberWeight_zero_pos_on_middleGap
      hlambda htau hfactor hq rho).le
  · rw [fiberWeight_eq_otherFactor hlambda.injective htau hfactor]
    exact div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr rho.property.1) hq.at_one_neg.le)
      (E_one_pos_of_strictMono hlambda).le
  · rw [fiberWeight_eq_otherFactor hlambda.injective htau hfactor]
    exact div_nonneg_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr rho.property.2) hq.at_two_neg.le)
      (E_two_neg_of_strictMono hlambda).le
  · exact (fiberWeight_three_pos_on_middleGap
      hlambda htau hfactor hq rho).le

/-- Every point of the closed middle-gap parameterization has at least three
strictly positive weights.  At the left endpoint node `1` vanishes, at the
right endpoint node `2` vanishes, and in the interior all four weights are
positive. -/
theorem three_le_card_positive_fiberWeight_on_middleGap
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {tau : ℝ} (htau : 0 < tau) {p q : MonicQuadratic}
    (hfactor : p.toPolynomial * q.toPolynomial =
      nodalQuartic lambda + C (tau ^ 2))
    (hq : OuterGapSignPattern lambda q)
    (rho : Icc (lambda 1) (lambda 2)) :
    3 ≤ (Finset.univ.filter fun i ↦
      0 < fiberWeight lambda tau (rho : ℝ) p i).card := by
  have hzero := fiberWeight_zero_pos_on_middleGap
    hlambda htau hfactor hq rho
  have hthree := fiberWeight_three_pos_on_middleGap
    hlambda htau hfactor hq rho
  by_cases hleft : (rho : ℝ) = lambda 1
  · have htwo : 0 < fiberWeight lambda tau (rho : ℝ) p 2 :=
      fiberWeight_two_pos_of_lt_right hlambda htau hfactor hq
        (by simpa [hleft] using (hlambda (by decide) : lambda 1 < lambda 2))
    have hsubset : ({0, 2, 3} : Finset (Fin 4)) ⊆
        Finset.univ.filter fun i ↦
          0 < fiberWeight lambda tau (rho : ℝ) p i := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hi with rfl | rfl | rfl
      · exact hzero
      · exact htwo
      · exact hthree
    simpa using Finset.card_le_card hsubset
  · have hone : 0 < fiberWeight lambda tau (rho : ℝ) p 1 :=
      fiberWeight_one_pos_of_left_lt hlambda htau hfactor hq
        (lt_of_le_of_ne rho.property.1 (Ne.symm hleft))
    have hsubset : ({0, 1, 3} : Finset (Fin 4)) ⊆
        Finset.univ.filter fun i ↦
          0 < fiberWeight lambda tau (rho : ℝ) p i := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hi with rfl | rfl | rfl
      · exact hzero
      · exact hone
      · exact hthree
    simpa using Finset.card_le_card hsubset

/-- The genuine simplex-valued point on the `p`-fiber at a middle-gap
parameter. -/
def AdmissibleFiberFactors.pPoint
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) : Weights :=
  fiberPoint lambda hlambda.injective tau h.tau_pos (rho : ℝ) p q
    h.factorization
    (fiberWeight_nonneg_on_middleGap
      hlambda h.tau_pos h.factorization h.q_signs rho)
    (three_le_card_positive_fiberWeight_on_middleGap
      hlambda h.tau_pos h.factorization h.q_signs rho)

@[simp]
theorem AdmissibleFiberFactors.pPoint_apply
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) (i : Fin 4) :
    h.pPoint hlambda rho i = fiberWeight lambda tau (rho : ℝ) p i :=
  rfl

/-- The companion simplex-valued point on the `q`-fiber at the same
middle-gap parameter. -/
def AdmissibleFiberFactors.qPoint
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) : Weights :=
  h.swap.pPoint hlambda rho

@[simp]
theorem AdmissibleFiberFactors.qPoint_apply
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) (i : Fin 4) :
    h.qPoint hlambda rho i = fiberWeight lambda tau (rho : ℝ) q i :=
  rfl

/-- The packaged point really belongs to the fixed `p`-fiber selected by its
parameter. -/
theorem AdmissibleFiberFactors.pPoint_memFiber
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) :
    MemFiber lambda tau (rho : ℝ) p (h.pPoint hlambda rho) := by
  intro i
  rfl

/-- The companion point belongs to the fixed `q`-fiber at the same
parameter. -/
theorem AdmissibleFiberFactors.qPoint_memFiber
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) :
    MemFiber lambda tau (rho : ℝ) q (h.qPoint hlambda rho) := by
  intro i
  rfl

theorem AdmissibleFiberFactors.P_pPoint
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) :
    P lambda (h.pPoint hlambda rho) = p :=
  P_eq_of_memFiber hlambda.injective h.tau_pos h.factorization
    (h.pPoint_memFiber hlambda rho)

theorem AdmissibleFiberFactors.P_qPoint
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) :
    P lambda (h.qPoint hlambda rho) = q :=
  P_eq_of_memFiber hlambda.injective h.tau_pos h.swap.factorization
    (h.qPoint_memFiber hlambda rho)

theorem AdmissibleFiberFactors.height_pPoint
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) :
    H lambda (h.pPoint hlambda rho) = tau ^ 2 :=
  height_eq_tau_sq_of_memFiber hlambda.injective h.tau_pos h.factorization
    (h.pPoint_memFiber hlambda rho)

theorem AdmissibleFiberFactors.height_qPoint
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda)
    (rho : Icc (lambda 1) (lambda 2)) :
    H lambda (h.qPoint hlambda rho) = tau ^ 2 :=
  height_eq_tau_sq_of_memFiber hlambda.injective h.tau_pos
    h.swap.factorization (h.qPoint_memFiber hlambda rho)

/-- The coefficient topology on the simplex, induced from its four concrete
weight coordinates. -/
instance instTopologicalSpaceWeights : TopologicalSpace Weights :=
  TopologicalSpace.induced weightVector inferInstance

theorem continuous_weightVector : Continuous weightVector :=
  continuous_induced_dom

instance instT2SpaceWeights : T2Space Weights :=
  T2Space.of_injective_continuous
    (fun _ _ hxy ↦ Weights.ext fun i ↦ congrFun hxy i)
    continuous_weightVector

theorem AdmissibleFiberFactors.continuous_pPoint
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) :
    Continuous (h.pPoint hlambda) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro i
  change Continuous (fun rho : Icc (lambda 1) (lambda 2) ↦
    fiberWeight lambda tau (rho : ℝ) p i)
  unfold fiberWeight
  fun_prop

theorem AdmissibleFiberFactors.continuous_qPoint
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) :
    Continuous (h.qPoint hlambda) :=
  h.swap.continuous_pPoint hlambda

/-- The complete closed `p`-fiber curve, parameterized by the closed middle
node gap and valued in the simplex rather than ambient coordinates. -/
def AdmissibleFiberFactors.pCurve
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) : Set Weights :=
  Set.range (h.pPoint hlambda)

/-- The complete closed companion `q`-fiber curve. -/
def AdmissibleFiberFactors.qCurve
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) : Set Weights :=
  Set.range (h.qPoint hlambda)

/-- Membership in the simplex-valued curve is precisely membership in one
of the fixed fibers as the parameter ranges over the closed middle gap. -/
theorem AdmissibleFiberFactors.mem_pCurve_iff
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) {x : Weights} :
    x ∈ h.pCurve hlambda ↔
      ∃ rho : Icc (lambda 1) (lambda 2),
        MemFiber lambda tau (rho : ℝ) p x := by
  constructor
  · rintro ⟨rho, rfl⟩
    exact ⟨rho, h.pPoint_memFiber hlambda rho⟩
  · rintro ⟨rho, hx⟩
    refine ⟨rho, ?_⟩
    apply Weights.ext
    intro i
    exact (h.pPoint_apply hlambda rho i).trans (hx i).symm

theorem AdmissibleFiberFactors.mem_qCurve_iff
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) {x : Weights} :
    x ∈ h.qCurve hlambda ↔
      ∃ rho : Icc (lambda 1) (lambda 2),
        MemFiber lambda tau (rho : ℝ) q x := by
  constructor
  · rintro ⟨rho, rfl⟩
    exact ⟨rho, h.qPoint_memFiber hlambda rho⟩
  · rintro ⟨rho, hx⟩
    refine ⟨rho, ?_⟩
    apply Weights.ext
    intro i
    exact (h.qPoint_apply hlambda rho i).trans (hx i).symm

theorem AdmissibleFiberFactors.isCompact_pCurve
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) :
    IsCompact (h.pCurve hlambda) :=
  isCompact_range (h.continuous_pPoint hlambda)

theorem AdmissibleFiberFactors.isClosed_pCurve
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) :
    IsClosed (h.pCurve hlambda) :=
  (h.isCompact_pCurve hlambda).isClosed

theorem AdmissibleFiberFactors.isCompact_qCurve
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) :
    IsCompact (h.qCurve hlambda) :=
  isCompact_range (h.continuous_qPoint hlambda)

theorem AdmissibleFiberFactors.isClosed_qCurve
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) :
    IsClosed (h.qCurve hlambda) :=
  (h.isCompact_qCurve hlambda).isClosed

/-- Exact root placement for a limiting quadratic: one root in each exterior
node gap, together with the monic linear-factor decomposition. -/
def OuterRootPlacement (lambda : Fin 4 → ℝ)
    (r : MonicQuadratic) : Prop :=
  ∃ leftRoot ∈ Ioo (lambda 0) (lambda 1),
    ∃ rightRoot ∈ Ioo (lambda 2) (lambda 3),
      r.toPolynomial.eval leftRoot = 0 ∧
      r.toPolynomial.eval rightRoot = 0 ∧
      r.toPolynomial =
        (X - C leftRoot) * (X - C rightRoot)

private theorem natDegree_monicQuadratic_fiberCurve (r : MonicQuadratic) :
    r.toPolynomial.natDegree = 2 := by
  rw [MonicQuadratic.toPolynomial]
  compute_degree <;> norm_num

/-- The admissible endpoint signs force the exact outer-gap root placement. -/
theorem OuterGapSignPattern.rootPlacement
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    {r : MonicQuadratic} (h : OuterGapSignPattern lambda r) :
    OuterRootPlacement lambda r := by
  have h01 : lambda 0 ≤ lambda 1 := (hlambda (by decide)).le
  have h23 : lambda 2 ≤ lambda 3 := (hlambda (by decide)).le
  have hzeroLeft : (0 : ℝ) ∈ Icc
      (r.toPolynomial.eval (lambda 1))
      (r.toPolynomial.eval (lambda 0)) :=
    ⟨h.at_one_neg.le, h.at_zero_pos.le⟩
  obtain ⟨leftRoot, hleftIcc, hleftEval⟩ :
      ∃ t ∈ Icc (lambda 0) (lambda 1),
        r.toPolynomial.eval t = 0 := by
    simpa only [Set.mem_image] using
      (intermediate_value_Icc' h01
        r.toPolynomial.continuous.continuousOn hzeroLeft)
  have hzeroRight : (0 : ℝ) ∈ Icc
      (r.toPolynomial.eval (lambda 2))
      (r.toPolynomial.eval (lambda 3)) :=
    ⟨h.at_two_neg.le, h.at_three_pos.le⟩
  obtain ⟨rightRoot, hrightIcc, hrightEval⟩ :
      ∃ t ∈ Icc (lambda 2) (lambda 3),
        r.toPolynomial.eval t = 0 := by
    simpa only [Set.mem_image] using
      (intermediate_value_Icc h23
        r.toPolynomial.continuous.continuousOn hzeroRight)
  have hleftMem : leftRoot ∈ Ioo (lambda 0) (lambda 1) := by
    refine ⟨lt_of_le_of_ne hleftIcc.1 ?_, lt_of_le_of_ne hleftIcc.2 ?_⟩
    · intro heq
      rw [← heq] at hleftEval
      exact (ne_of_gt h.at_zero_pos) hleftEval
    · intro heq
      rw [heq] at hleftEval
      exact (ne_of_lt h.at_one_neg) hleftEval
  have hrightMem : rightRoot ∈ Ioo (lambda 2) (lambda 3) := by
    refine ⟨lt_of_le_of_ne hrightIcc.1 ?_, lt_of_le_of_ne hrightIcc.2 ?_⟩
    · intro heq
      rw [← heq] at hrightEval
      exact (ne_of_lt h.at_two_neg) hrightEval
    · intro heq
      rw [heq] at hrightEval
      exact (ne_of_gt h.at_three_pos) hrightEval
  have hrootNe : leftRoot ≠ rightRoot :=
    ne_of_lt (hleftMem.2.trans
      ((hlambda (by decide)).trans hrightMem.1))
  have hdvdLeft : X - C leftRoot ∣ r.toPolynomial := by
    rw [dvd_iff_isRoot, IsRoot]
    exact hleftEval
  have hdvdRight : X - C rightRoot ∣ r.toPolynomial := by
    rw [dvd_iff_isRoot, IsRoot]
    exact hrightEval
  have hcoprime : IsCoprime (X - C leftRoot : ℝ[X])
      (X - C rightRoot) :=
    isCoprime_X_sub_C_of_isUnit_sub
      ((sub_ne_zero.mpr hrootNe).isUnit)
  have hdvd : (X - C leftRoot) * (X - C rightRoot) ∣
      r.toPolynomial :=
    hcoprime.mul_dvd hdvdLeft hdvdRight
  have hproductMonic :
      ((X - C leftRoot) * (X - C rightRoot) : ℝ[X]).Monic :=
    (monic_X_sub_C leftRoot).mul (monic_X_sub_C rightRoot)
  have hproductDegree :
      ((X - C leftRoot) * (X - C rightRoot) : ℝ[X]).natDegree = 2 := by
    rw [(monic_X_sub_C leftRoot).natDegree_mul
      (monic_X_sub_C rightRoot), natDegree_X_sub_C, natDegree_X_sub_C]
  have hfactor : r.toPolynomial =
      (X - C leftRoot) * (X - C rightRoot) := by
    apply eq_of_monic_of_dvd_of_natDegree_le hproductMonic
      (MonicQuadratic.monic r) hdvd
    rw [natDegree_monicQuadratic_fiberCurve, hproductDegree]
  exact ⟨leftRoot, hleftMem, rightRoot, hrightMem,
    hleftEval, hrightEval, hfactor⟩

theorem AdmissibleFiberFactors.pRootPlacement
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) : OuterRootPlacement lambda p :=
  h.p_signs.rootPlacement hlambda

theorem AdmissibleFiberFactors.qRootPlacement
    {lambda : Fin 4 → ℝ} {tau : ℝ} {p q : MonicQuadratic}
    (h : AdmissibleFiberFactors lambda tau p q)
    (hlambda : StrictMono lambda) : OuterRootPlacement lambda q :=
  h.q_signs.rootPlacement hlambda

end

end FourNode
end Forsythe
