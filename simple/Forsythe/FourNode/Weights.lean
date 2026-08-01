import Forsythe.Polynomial.Lagrange
import Forsythe.Polynomial.Quadratic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card

/-!
# The four-node weight simplex and its exact update

This module is the finite-node model used in the four-node closure argument.
Weights are nonnegative, normalized, and have at least three positive entries.
All moments, the orthogonal monic quadratic, its height, and the normalized
update are given by explicit finite sums and rational formulas.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Polynomial
open scoped BigOperators

noncomputable section

/-- Normalized four-node weights with at least three positive entries. -/
structure Weights where
  /-- The nonnegative mass assigned to each of the four nodes. -/
  weight : Fin 4 → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  sum_eq_one : ∑ i, weight i = 1
  three_le_card_positive :
    3 ≤ (Finset.univ.filter fun i ↦ 0 < weight i).card

instance : CoeFun Weights (fun _ ↦ Fin 4 → ℝ) :=
  ⟨Weights.weight⟩

/-- Two weight states are equal when all four scalar weights agree. -/
@[ext]
theorem Weights.ext {x y : Weights} (h : ∀ i, x i = y i) : x = y := by
  cases x with
  | mk x hxNonneg hxSum hxCard =>
      cases y with
      | mk y hyNonneg hySum hyCard =>
          have hxy : x = y := funext h
          subst y
          rfl

/-- Every normalized nonnegative weight is at most one. -/
theorem weight_le_one (x : Weights) (i : Fin 4) : x i ≤ 1 := by
  rw [← x.sum_eq_one]
  exact Finset.single_le_sum (fun j _ ↦ x.nonneg j) (Finset.mem_univ i)

/-- Indices carrying positive weight. -/
def positiveSupport (x : Weights) : Finset (Fin 4) :=
  Finset.univ.filter fun i ↦ 0 < x i

@[simp]
theorem mem_positiveSupport_iff (x : Weights) (i : Fin 4) :
    i ∈ positiveSupport x ↔ 0 < x i := by
  simp [positiveSupport]

theorem three_le_card_positiveSupport (x : Weights) :
    3 ≤ (positiveSupport x).card :=
  x.three_le_card_positive

/-- The `k`th moment of the four weighted nodes. -/
def weightedMoment (lambda : Fin 4 → ℝ) (x : Weights) (k : ℕ) : ℝ :=
  ∑ i, x i * lambda i ^ k

@[simp]
theorem weightedMoment_zero (lambda : Fin 4 → ℝ) (x : Weights) :
    weightedMoment lambda x 0 = 1 := by
  simpa [weightedMoment] using x.sum_eq_one

/-- Determinant of the weighted moment Gram matrix of `1,z`. -/
def weightedMomentGramDet (lambda : Fin 4 → ℝ) (x : Weights) : ℝ :=
  weightedMoment lambda x 0 * weightedMoment lambda x 2 -
    weightedMoment lambda x 1 ^ 2

/-- Weighted polynomial inner product in manuscript notation. -/
def weightedPolyInner (lambda : Fin 4 → ℝ) (x : Weights)
    (p q : Polynomial ℝ) : ℝ :=
  ∑ i, x i * p.eval (lambda i) * q.eval (lambda i)

/-- The explicit Cramer-system monic quadratic `P_x`. -/
def orthogonalPolynomial (lambda : Fin 4 → ℝ) (x : Weights) :
    MonicQuadratic where
  linearCoeff :=
    (weightedMoment lambda x 1 * weightedMoment lambda x 2 -
      weightedMoment lambda x 0 * weightedMoment lambda x 3) /
        weightedMomentGramDet lambda x
  constantCoeff :=
    (weightedMoment lambda x 1 * weightedMoment lambda x 3 -
      weightedMoment lambda x 2 ^ 2) /
        weightedMomentGramDet lambda x

/-- Manuscript notation `P_x`. -/
abbrev P := orthogonalPolynomial

/-- The squared residual height `H(x)`. -/
def height (lambda : Fin 4 → ℝ) (x : Weights) : ℝ :=
  weightedPolyInner lambda x (P lambda x).toPolynomial
    (P lambda x).toPolynomial

/-- Manuscript notation `H(x)`. -/
abbrev H := height

private theorem weighted_variance_identity (lambda : Fin 4 → ℝ) (x : Weights) :
    ∑ i, x i * (lambda i - weightedMoment lambda x 1) ^ 2 =
      weightedMomentGramDet lambda x := by
  let m := weightedMoment lambda x 1
  have hsum : ∑ i, x i = 1 := x.sum_eq_one
  calc
    ∑ i, x i * (lambda i - weightedMoment lambda x 1) ^ 2 =
        ∑ i, x i * lambda i ^ 2 -
          2 * m * (∑ i, x i * lambda i) +
            m ^ 2 * (∑ i, x i) := by
      calc
        ∑ i, x i * (lambda i - weightedMoment lambda x 1) ^ 2 =
            ∑ i, (x i * lambda i ^ 2 -
              2 * m * (x i * lambda i) + m ^ 2 * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [m]
          ring
        _ = ∑ i, x i * lambda i ^ 2 -
            2 * m * (∑ i, x i * lambda i) +
              m ^ 2 * (∑ i, x i) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          simp only [Finset.mul_sum]
    _ = weightedMomentGramDet lambda x := by
      simp only [weightedMomentGramDet, weightedMoment, pow_zero, pow_one, mul_one]
      dsimp only [m, weightedMoment]
      rw [hsum]
      ring_nf

/-- Three positive weights at distinct nodes make the weighted moment Gram
matrix strictly positive. -/
theorem weightedMomentGramDet_pos
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    0 < weightedMomentGramDet lambda x := by
  have hone : 1 < (positiveSupport x).card := by
    exact lt_of_lt_of_le (by norm_num) (three_le_card_positiveSupport x)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hone
  have hxa : 0 < x a := (mem_positiveSupport_iff x a).mp ha
  have hxb : 0 < x b := (mem_positiveSupport_iff x b).mp hb
  let m := weightedMoment lambda x 1
  have hnode : lambda a ≠ m ∨ lambda b ≠ m := by
    by_contra h
    push Not at h
    exact hab (hlambda (h.1.trans h.2.symm))
  have hterm : ∃ i ∈ (Finset.univ : Finset (Fin 4)),
      0 < x i * (lambda i - m) ^ 2 := by
    rcases hnode with haNode | hbNode
    · exact ⟨a, Finset.mem_univ _, mul_pos hxa (sq_pos_of_ne_zero (sub_ne_zero.mpr haNode))⟩
    · exact ⟨b, Finset.mem_univ _, mul_pos hxb (sq_pos_of_ne_zero (sub_ne_zero.mpr hbNode))⟩
  rw [← weighted_variance_identity lambda x]
  exact Finset.sum_pos'
    (fun i _ ↦ mul_nonneg (x.nonneg i) (sq_nonneg _)) hterm

theorem weightedMomentGramDet_ne_zero
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    weightedMomentGramDet lambda x ≠ 0 :=
  ne_of_gt (weightedMomentGramDet_pos hlambda x)

private theorem weightedPolyInner_monic_one
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

private theorem weightedPolyInner_monic_X
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

/-- `P_x` is weighted-orthogonal to the constant polynomial. -/
theorem P_orthogonal_one
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    weightedPolyInner lambda x (P lambda x).toPolynomial 1 = 0 := by
  rw [weightedPolyInner_monic_one]
  simp only [P, orthogonalPolynomial]
  field_simp [weightedMomentGramDet_ne_zero hlambda x]
  simp only [weightedMomentGramDet]
  ring

/-- `P_x` is weighted-orthogonal to `z`. -/
theorem P_orthogonal_X
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    weightedPolyInner lambda x (P lambda x).toPolynomial X = 0 := by
  rw [weightedPolyInner_monic_X]
  simp only [P, orthogonalPolynomial]
  field_simp [weightedMomentGramDet_ne_zero hlambda x]
  simp only [weightedMomentGramDet]
  ring

private theorem natDegree_monicQuadratic (p : MonicQuadratic) :
    p.toPolynomial.natDegree = 2 := by
  have hle : p.toPolynomial.natDegree ≤ 2 := by
    rw [MonicQuadratic.toPolynomial]
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · simp
      · simpa only [pow_one] using
          (natDegree_C_mul_X_pow_le p.linearCoeff 1).trans (by norm_num : 1 ≤ 2)
    · simp
  have hge : 2 ≤ p.toPolynomial.natDegree :=
    le_natDegree_of_ne_zero (by simp)
  exact le_antisymm hle hge

private theorem exists_positive_P_eval_ne_zero
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    ∃ i, 0 < x i ∧ (P lambda x).toPolynomial.eval (lambda i) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let s := positiveSupport x
  let imageNodes : Finset ℝ := s.image lambda
  have himageCard : imageNodes.card = s.card :=
    Finset.card_image_of_injective _ hlambda
  have hrootSubset : imageNodes ⊆ (P lambda x).toPolynomial.roots.toFinset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    rw [Multiset.mem_toFinset,
      Polynomial.mem_roots (MonicQuadratic.monic (P lambda x)).ne_zero,
      Polynomial.IsRoot]
    exact h i ((mem_positiveSupport_iff x i).mp hi)
  have hcardRoots : s.card ≤ (P lambda x).toPolynomial.natDegree := by
    calc
      s.card = imageNodes.card := himageCard.symm
      _ ≤ (P lambda x).toPolynomial.roots.toFinset.card :=
        Finset.card_le_card hrootSubset
      _ ≤ (P lambda x).toPolynomial.roots.card :=
        Multiset.toFinset_card_le _
      _ ≤ (P lambda x).toPolynomial.natDegree := Polynomial.card_roots' _
  rw [natDegree_monicQuadratic] at hcardRoots
  have := three_le_card_positiveSupport x
  change 3 ≤ s.card at this
  omega

/-- The residual height is strictly positive, also at a boundary state with
exactly three positive weights. -/
theorem height_pos
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    0 < H lambda x := by
  obtain ⟨i, hxi, hPi⟩ := exists_positive_P_eval_ne_zero hlambda x
  change 0 < weightedPolyInner lambda x (P lambda x).toPolynomial
    (P lambda x).toPolynomial
  rw [weightedPolyInner]
  exact Finset.sum_pos'
    (fun j _ ↦ by
      nlinarith [x.nonneg j,
        sq_nonneg ((P lambda x).toPolynomial.eval (lambda j))])
    ⟨i, Finset.mem_univ _, by
      have hsquare : 0 < (P lambda x).toPolynomial.eval (lambda i) ^ 2 :=
        sq_pos_of_ne_zero hPi
      nlinarith⟩

/-- One normalized squared-weight update, before packaging its simplex
proofs. -/
def nextWeight (lambda : Fin 4 → ℝ) (x : Weights) (i : Fin 4) : ℝ :=
  x i * (P lambda x).toPolynomial.eval (lambda i) ^ 2 / H lambda x

theorem nextWeight_nonneg
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    0 ≤ nextWeight lambda x i := by
  exact div_nonneg (mul_nonneg (x.nonneg i) (sq_nonneg _))
    (height_pos hlambda x).le

theorem sum_nextWeight
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    ∑ i, nextWeight lambda x i = 1 := by
  simp only [nextWeight, height, weightedPolyInner, pow_two, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hsumEq :
      (∑ i, x i *
        ((P lambda x).toPolynomial.eval (lambda i) *
          (P lambda x).toPolynomial.eval (lambda i))) = H lambda x := by
    change (∑ i, x i *
        ((P lambda x).toPolynomial.eval (lambda i) *
          (P lambda x).toPolynomial.eval (lambda i))) =
      weightedPolyInner lambda x (P lambda x).toPolynomial
        (P lambda x).toPolynomial
    rw [weightedPolyInner]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsumEq]
  exact mul_inv_cancel₀ (ne_of_gt (height_pos hlambda x))

private def nonzeroSupport (y : Fin 4 → ℝ) : Finset (Fin 4) :=
  Finset.univ.filter fun i ↦ y i ≠ 0

private theorem sparse_two_moment_zero
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (y : Fin 4 → ℝ)
    (hsum : ∑ i, y i = 0) (hsumLambda : ∑ i, lambda i * y i = 0)
    (hcard : (nonzeroSupport y).card ≤ 2) :
    y = 0 := by
  classical
  let s := nonzeroSupport y
  have hsumS : ∑ i ∈ s, y i = 0 := by
    rw [← hsum]
    exact Finset.sum_subset (Finset.subset_univ s) fun i _ hi ↦ by
      simpa [s, nonzeroSupport] using hi
  have hsumLambdaS : ∑ i ∈ s, lambda i * y i = 0 := by
    rw [← hsumLambda]
    exact Finset.sum_subset (Finset.subset_univ s) fun i _ hi ↦ by
      have hy : y i = 0 := by simpa [s, nonzeroSupport] using hi
      rw [hy, mul_zero]
  have houtside (i : Fin 4) (hi : i ∉ s) : y i = 0 := by
    by_contra hy
    exact hi (by simp [s, nonzeroSupport, hy])
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by
    change s.card ≤ 2 at hcard
    omega
  rcases hcases with hzero | hone | htwo
  · have hs : s = ∅ := Finset.card_eq_zero.mp hzero
    funext i
    exact houtside i (by simp [hs])
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
    have hya : y a = 0 := by simpa [ha] using hsumS
    funext i
    by_cases hia : i = a
    · simpa [hia] using hya
    · exact houtside i (by simp [ha, hia])
  · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp htwo
    have habNodes : lambda a ≠ lambda b := hlambda.ne hab
    have hsumAB : y a + y b = 0 := by simpa [hs, hab] using hsumS
    have hsumLambdaAB : lambda a * y a + lambda b * y b = 0 := by
      simpa [hs, hab] using hsumLambdaS
    have hya : y a = 0 := by
      have hmul : (lambda a - lambda b) * y a = 0 := by
        linear_combination hsumLambdaAB - lambda b * hsumAB
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr habNodes)
    have hyb : y b = 0 := by linarith
    funext i
    by_cases hia : i = a
    · simpa [hia] using hya
    · by_cases hib : i = b
      · simpa [hib] using hyb
      · exact houtside i (by simp [hs, hia, hib])

private theorem three_le_card_nonzero_residual
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    3 ≤ (nonzeroSupport (fun i ↦
      x i * (P lambda x).toPolynomial.eval (lambda i))).card := by
  let y : Fin 4 → ℝ := fun i ↦
    x i * (P lambda x).toPolynomial.eval (lambda i)
  change 3 ≤ (nonzeroSupport y).card
  by_contra hthree
  have hcard : (nonzeroSupport y).card ≤ 2 := by omega
  have hsum : ∑ i, y i = 0 := by
    simpa [y, weightedPolyInner, mul_assoc] using P_orthogonal_one hlambda x
  have hsumLambda : ∑ i, lambda i * y i = 0 := by
    have horth := P_orthogonal_X hlambda x
    simp only [weightedPolyInner, eval_X] at horth
    simpa [y, mul_assoc, mul_left_comm, mul_comm] using horth
  have hyzero := sparse_two_moment_zero hlambda y hsum hsumLambda hcard
  have hHzero : H lambda x = 0 := by
    change weightedPolyInner lambda x (P lambda x).toPolynomial
      (P lambda x).toPolynomial = 0
    rw [weightedPolyInner]
    apply Finset.sum_eq_zero
    intro i _
    have hi := congrFun hyzero i
    dsimp only [y] at hi
    have hi' : x i * (P lambda x).toPolynomial.eval (lambda i) = 0 := by
      simpa using hi
    calc
      x i * (P lambda x).toPolynomial.eval (lambda i) *
          (P lambda x).toPolynomial.eval (lambda i) =
        (x i * (P lambda x).toPolynomial.eval (lambda i)) *
          (P lambda x).toPolynomial.eval (lambda i) := by ring
      _ = 0 := by rw [hi', zero_mul]
  exact (ne_of_gt (height_pos hlambda x)) hHzero

/-- A normalized update is positive exactly where the old weighted residual
is nonzero. -/
theorem nextWeight_pos_iff
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    0 < nextWeight lambda x i ↔
      x i * (P lambda x).toPolynomial.eval (lambda i) ≠ 0 := by
  have hH := height_pos hlambda x
  rw [nextWeight, div_pos_iff]
  simp only [hH, and_true, not_lt_of_ge hH.le, and_false, or_false]
  constructor
  · intro hprod
    have hxne : x i ≠ 0 := by
      intro hx
      rw [hx, zero_mul] at hprod
      exact (lt_irrefl 0) hprod
    have hpne : (P lambda x).toPolynomial.eval (lambda i) ≠ 0 := by
      intro hp
      simp [hp] at hprod
    exact mul_ne_zero hxne hpne
  · intro hne
    have hxne : x i ≠ 0 := (mul_ne_zero_iff.mp hne).1
    have hpne : (P lambda x).toPolynomial.eval (lambda i) ≠ 0 :=
      (mul_ne_zero_iff.mp hne).2
    exact mul_pos (lt_of_le_of_ne (x.nonneg i) (Ne.symm hxne))
      (sq_pos_of_ne_zero hpne)

/-- The normalized update retains at least three positive weights, including
when the input has exactly three positive weights. -/
theorem three_le_card_positive_nextWeight
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : Weights) :
    3 ≤ (Finset.univ.filter fun i ↦ 0 < nextWeight lambda x i).card := by
  have heq :
      (Finset.univ.filter fun i ↦ 0 < nextWeight lambda x i) =
        nonzeroSupport (fun i ↦
          x i * (P lambda x).toPolynomial.eval (lambda i)) := by
    ext i
    simp [nonzeroSupport, nextWeight_pos_iff hlambda x i]
  rw [heq]
  exact three_le_card_nonzero_residual hlambda x

/-- The exact normalized four-node map `T(x)`. -/
def T (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) : Weights where
  weight := nextWeight lambda x
  nonneg := nextWeight_nonneg hlambda x
  sum_eq_one := sum_nextWeight hlambda x
  three_le_card_positive := three_le_card_positive_nextWeight hlambda x

/-- Exact squared-weight update identity. -/
@[simp]
theorem T_weight
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    T lambda hlambda x i =
      x i * (P lambda x).toPolynomial.eval (lambda i) ^ 2 / H lambda x :=
  rfl

/-- Denominator-cleared form of the exact squared-weight update. -/
theorem height_mul_T_weight
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    H lambda x * T lambda hlambda x i =
      x i * (P lambda x).toPolynomial.eval (lambda i) ^ 2 := by
  rw [T_weight]
  field_simp [ne_of_gt (height_pos hlambda x)]

@[simp, nolint simpNF]
theorem T_weight_pos_iff
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (x : Weights) (i : Fin 4) :
    0 < T lambda hlambda x i ↔
      x i * (P lambda x).toPolynomial.eval (lambda i) ≠ 0 :=
  nextWeight_pos_iff hlambda x i

/-- Ordered nodes discharge the distinct-node hypothesis. -/
def TOfStrictMono (lambda : Fin 4 → ℝ) (hlambda : StrictMono lambda)
    (x : Weights) : Weights :=
  T lambda hlambda.injective x

end

end FourNode
end Forsythe
