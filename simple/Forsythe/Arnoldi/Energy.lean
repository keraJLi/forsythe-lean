import Forsythe.Arnoldi.Step
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Orbit-level energy laws for restart-two Arnoldi steps

This module lifts the two-step algebraic identities to sequences.  It deliberately keeps the
conditional step relation separate from determinism: `IsQuadraticStepSequence` supplies the
energy laws, while eventual two-periodicity additionally assumes that the vector sequence is an
orbit of one fixed update map.
-/

set_option autoImplicit false

namespace Forsythe

noncomputable section

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A sequence of vectors, monic quadratics, and positive normalizers satisfying the conditional
quadratic-step relation at every index. -/
structure IsQuadraticStepSequence (A : Module.End ℝ E) (v : ℕ → E)
    (p : ℕ → MonicQuadratic) (σ : ℕ → ℝ) : Prop where
  step : ∀ k, IsQuadraticStep A (v k) (v (k + 1)) (p k) (σ k)

/-- The manuscript's height `H_k = σ_k²`. -/
def quadraticStepHeight (σ : ℕ → ℝ) (k : ℕ) : ℝ :=
  σ k ^ 2

/-- The squared polynomial-remainder energy at the start of the two steps `k,k+1`. -/
def quadraticStepEnergy (A : Module.End ℝ E) (v : ℕ → E)
    (p : ℕ → MonicQuadratic) (σ : ℕ → ℝ) (k : ℕ) : ℝ :=
  let Q := (p k).toPolynomial * (p (k + 1)).toPolynomial
  let R := Q - Polynomial.C (σ k ^ 2)
  polyInner A (v k) R R

theorem quadraticStepHeight_nonneg (σ : ℕ → ℝ) (k : ℕ) :
    0 ≤ quadraticStepHeight σ k :=
  sq_nonneg (σ k)

theorem quadraticStepEnergy_nonneg (A : Module.End ℝ E) (v : ℕ → E)
    (p : ℕ → MonicQuadratic) (σ : ℕ → ℝ) (k : ℕ) :
    0 ≤ quadraticStepEnergy A v p σ k := by
  simp only [quadraticStepEnergy, polyInner]
  exact real_inner_self_nonneg

namespace IsQuadraticStepSequence

variable {A : Module.End ℝ E} {v : ℕ → E}
  {p : ℕ → MonicQuadratic} {σ : ℕ → ℝ}

theorem sigma_pos (h : IsQuadraticStepSequence A v p σ) (k : ℕ) :
    0 < σ k :=
  (h.step k).sigma_pos

theorem sigma_ne (h : IsQuadraticStepSequence A v p σ) (k : ℕ) :
    σ k ≠ 0 :=
  (h.step k).sigma_ne

/-- All vectors in a conditional step sequence have unit norm. -/
theorem norm_eq_one (h : IsQuadraticStepSequence A v p σ) (k : ℕ) :
    ‖v k‖ = 1 := by
  have hunit := (h.step k).source_unit
  rw [polyInner_one_one] at hunit
  nlinarith [norm_nonneg (v k)]

/-- Sequence-level form of the exact energy identity. -/
theorem energy_identity (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) (k : ℕ) :
    quadraticStepEnergy A v p σ k =
      quadraticStepHeight σ k *
        (quadraticStepHeight σ (k + 1) - quadraticStepHeight σ k) := by
  simpa only [quadraticStepEnergy, quadraticStepHeight] using
    quadraticStep_energy A hA (h.step k) (h.step (k + 1))

/-- The heights are nondecreasing at each step. -/
theorem height_le_succ (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) (k : ℕ) :
    quadraticStepHeight σ k ≤ quadraticStepHeight σ (k + 1) := by
  have henergy := quadraticStepEnergy_nonneg A v p σ k
  have hid := h.energy_identity hA k
  have hheight_pos : 0 < quadraticStepHeight σ k := by
    exact sq_pos_of_pos (h.sigma_pos k)
  nlinarith

theorem height_monotone (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) : Monotone (quadraticStepHeight σ) :=
  monotone_nat_of_le_succ (h.height_le_succ hA)

/-- Positivity of the normalizers upgrades monotonicity of their squares to monotonicity of the
normalizers themselves. -/
theorem sigma_le_succ (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) (k : ℕ) : σ k ≤ σ (k + 1) := by
  have hsquares := h.height_le_succ hA k
  have hk := h.sigma_pos k
  have hk1 := h.sigma_pos (k + 1)
  simp only [quadraticStepHeight] at hsquares
  nlinarith

theorem sigma_monotone (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) : Monotone σ :=
  monotone_nat_of_le_succ (h.sigma_le_succ hA)

/-- Sequence-level form of the two-step correlation identity. -/
theorem two_step_correlation (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) (k : ℕ) :
    inner ℝ (v k) (v (k + 2)) = σ k / σ (k + 1) := by
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    quadraticStep_correlation A hA (h.step k) (h.step (k + 1))

/-- Energy vanishes exactly when two consecutive heights agree. -/
theorem energy_eq_zero_iff_height_eq (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) (k : ℕ) :
    quadraticStepEnergy A v p σ k = 0 ↔
      quadraticStepHeight σ (k + 1) = quadraticStepHeight σ k := by
  rw [h.energy_identity hA k]
  constructor
  · intro hz
    have hp : 0 < quadraticStepHeight σ k := sq_pos_of_pos (h.sigma_pos k)
    rcases mul_eq_zero.mp hz with hz | hz
    · exact False.elim (ne_of_gt hp hz)
    · exact sub_eq_zero.mp hz
  · intro heq
    rw [heq, sub_self, mul_zero]

/-- Since all normalizers are positive, equality of heights is equality of normalizers. -/
theorem height_eq_iff_sigma_eq (h : IsQuadraticStepSequence A v p σ) (k : ℕ) :
    quadraticStepHeight σ (k + 1) = quadraticStepHeight σ k ↔
      σ (k + 1) = σ k := by
  simp only [quadraticStepHeight]
  constructor
  · intro hsquares
    have hk := h.sigma_pos k
    have hk1 := h.sigma_pos (k + 1)
    nlinarith
  · exact fun heq ↦ congrArg (fun x : ℝ ↦ x ^ 2) heq

/-- Equality of consecutive normalizers is equivalent to exact return after two vector steps. -/
theorem sigma_eq_iff_two_step_eq (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) (k : ℕ) :
    σ (k + 1) = σ k ↔ v (k + 2) = v k := by
  constructor
  · intro hsigma
    have hinner : inner ℝ (v k) (v (k + 2)) = 1 := by
      rw [h.two_step_correlation hA k, hsigma, div_self (h.sigma_ne k)]
    exact ((inner_eq_one_iff_of_norm_eq_one (h.norm_eq_one k)
      (h.norm_eq_one (k + 2))).mp hinner).symm
  · intro hvectors
    have hinner : inner ℝ (v k) (v (k + 2)) = 1 := by
      rw [hvectors, real_inner_self_eq_norm_sq, h.norm_eq_one k]
      norm_num
    have hratio : σ k / σ (k + 1) = 1 :=
      (h.two_step_correlation hA k).symm.trans hinner
    exact ((div_eq_one_iff_eq (h.sigma_ne (k + 1))).mp hratio).symm

/-- Equality in height monotonicity is precisely exact two-step return of the vector. -/
theorem height_eq_iff_two_step_eq (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) (k : ℕ) :
    quadraticStepHeight σ (k + 1) = quadraticStepHeight σ k ↔
      v (k + 2) = v k :=
  (h.height_eq_iff_sigma_eq k).trans (h.sigma_eq_iff_two_step_eq hA k)

/-- Equality in the energy law is precisely exact two-step return of the vector. -/
theorem energy_eq_zero_iff_two_step_eq (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) (k : ℕ) :
    quadraticStepEnergy A v p σ k = 0 ↔ v (k + 2) = v k :=
  (h.energy_eq_zero_iff_height_eq hA k).trans (h.height_eq_iff_two_step_eq hA k)

end IsQuadraticStepSequence

/-- Finite telescoping identity for the height increments. -/
theorem sum_quadraticStepHeight_increment (σ : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n,
        (quadraticStepHeight σ (k + 1) - quadraticStepHeight σ k) =
      quadraticStepHeight σ n - quadraticStepHeight σ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

namespace IsQuadraticStepSequence

variable {A : Module.End ℝ E} {v : ℕ → E}
  {p : ℕ → MonicQuadratic} {σ : ℕ → ℝ}

/-- A uniform upper bound on the heights makes their nonnegative increments summable. -/
theorem summable_height_increment (h : IsQuadraticStepSequence A v p σ)
    (hA : A.IsSymmetric) {M : ℝ} (hbound : ∀ k, quadraticStepHeight σ k ≤ M) :
    Summable (fun k ↦ quadraticStepHeight σ (k + 1) - quadraticStepHeight σ k) := by
  apply summable_of_sum_range_le (c := M)
  · exact fun k ↦ sub_nonneg.mpr (h.height_le_succ hA k)
  · intro n
    rw [sum_quadraticStepHeight_increment]
    have hzero := quadraticStepHeight_nonneg σ 0
    linarith [hbound n]

end IsQuadraticStepSequence

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- For an orbit of one fixed update map, a two-step return propagates forever. -/
theorem eventually_two_periodic_of_deterministic
    {v : ℕ → E} {T : E → E} (horbit : ∀ n, v (n + 1) = T (v n))
    {k : ℕ} (hk : v (k + 2) = v k) :
    ∀ n, k ≤ n → v (n + 2) = v n := by
  intro n hkn
  induction n, hkn using Nat.le_induction with
  | base => exact hk
  | succ n hn ih =>
      calc
        v ((n + 1) + 2) = v ((n + 2) + 1) := rfl
        _ = T (v (n + 2)) := horbit (n + 2)
        _ = T (v n) := by rw [ih]
        _ = v (n + 1) := (horbit n).symm

/-- Vanishing energy forces eventual exact two-periodicity when the conditional step sequence is
also generated by one deterministic vector update. -/
theorem IsQuadraticStepSequence.eventually_two_periodic_of_energy_eq_zero
    {A : Module.End ℝ E} {v : ℕ → E} {p : ℕ → MonicQuadratic} {σ : ℕ → ℝ}
    (h : IsQuadraticStepSequence A v p σ) (hA : A.IsSymmetric)
    {T : E → E} (horbit : ∀ n, v (n + 1) = T (v n))
    {k : ℕ} (henergy : quadraticStepEnergy A v p σ k = 0) :
    ∀ n, k ≤ n → v (n + 2) = v n :=
  eventually_two_periodic_of_deterministic horbit <|
    (h.energy_eq_zero_iff_two_step_eq hA k).mp henergy

end

end Forsythe
