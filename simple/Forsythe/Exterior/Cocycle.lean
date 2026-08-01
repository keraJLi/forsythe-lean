import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic

/-!
# Logarithmic cocycles for squared weight recurrences

Positive squared-component weights evolve multiplicatively over two steps.
Taking logarithms converts the exterior/principal product cocycle into an
exact additive increment.  The order lemmas at the end isolate the
contradiction used in the exterior-decay argument: an eventually strictly
increasing parity cocycle cannot escape to minus infinity, even along a
cofinal subsequence.
-/

set_option autoImplicit false

namespace Forsythe
namespace Exterior

open Filter Set Topology
open scoped BigOperators

noncomputable section

/-- Exact positive two-step recurrences for one exterior weight and a finite
family of principal weights.  The multipliers are component multipliers, so
the squared weights acquire their squares. -/
structure IsTwoStepSquaredWeightUpdate {ι : Type*}
    (exteriorWeight : ℕ → ℝ) (principalWeight : ι → ℕ → ℝ)
    (exteriorMultiplier : ℕ → ℝ) (principalMultiplier : ι → ℕ → ℝ) : Prop where
  exteriorWeight_pos : ∀ k, 0 < exteriorWeight k
  principalWeight_pos : ∀ i k, 0 < principalWeight i k
  exteriorMultiplier_pos : ∀ k, 0 < exteriorMultiplier k
  principalMultiplier_pos : ∀ i k, 0 < principalMultiplier i k
  exterior_update : ∀ k,
    exteriorWeight (k + 2) = exteriorMultiplier k ^ 2 * exteriorWeight k
  principal_update : ∀ i k,
    principalWeight i (k + 2) =
      principalMultiplier i k ^ 2 * principalWeight i k

/-- The logarithmic exterior/principal cocycle. -/
def logarithmicWeightCocycle {ι : Type*} [Fintype ι]
    (exteriorWeight : ℕ → ℝ) (principalWeight : ι → ℕ → ℝ)
    (beta : ι → ℝ) (k : ℕ) : ℝ :=
  Real.log (exteriorWeight k) +
    ∑ i, beta i * Real.log (principalWeight i k)

/-- Exact two-step cocycle increment, expressed using the squared component
multipliers. -/
theorem logarithmicWeightCocycle_add_two_sub
    {ι : Type*} [Fintype ι]
    (exteriorWeight : ℕ → ℝ) (principalWeight : ι → ℕ → ℝ)
    (exteriorMultiplier : ℕ → ℝ) (principalMultiplier : ι → ℕ → ℝ)
    (beta : ι → ℝ)
    (hupdate : IsTwoStepSquaredWeightUpdate exteriorWeight principalWeight
      exteriorMultiplier principalMultiplier)
    (k : ℕ) :
    logarithmicWeightCocycle exteriorWeight principalWeight beta (k + 2) -
        logarithmicWeightCocycle exteriorWeight principalWeight beta k =
      Real.log (exteriorMultiplier k ^ 2) +
        ∑ i, beta i * Real.log (principalMultiplier i k ^ 2) := by
  have hlogExterior :
      Real.log (exteriorWeight (k + 2)) =
        Real.log (exteriorMultiplier k ^ 2) +
          Real.log (exteriorWeight k) := by
    rw [hupdate.exterior_update k]
    exact Real.log_mul
      (pow_ne_zero 2 (ne_of_gt (hupdate.exteriorMultiplier_pos k)))
      (ne_of_gt (hupdate.exteriorWeight_pos k))
  have hlogPrincipal (i : ι) :
      Real.log (principalWeight i (k + 2)) =
        Real.log (principalMultiplier i k ^ 2) +
          Real.log (principalWeight i k) := by
    rw [hupdate.principal_update i k]
    exact Real.log_mul
      (pow_ne_zero 2 (ne_of_gt (hupdate.principalMultiplier_pos i k)))
      (ne_of_gt (hupdate.principalWeight_pos i k))
  simp only [logarithmicWeightCocycle, hlogExterior, hlogPrincipal, mul_add,
    Finset.sum_add_distrib]
  ring

/-- Equivalent increment formula with the factor `2` pulled outside each
logarithm. -/
theorem logarithmicWeightCocycle_add_two_sub_eq_two_mul_log
    {ι : Type*} [Fintype ι]
    (exteriorWeight : ℕ → ℝ) (principalWeight : ι → ℕ → ℝ)
    (exteriorMultiplier : ℕ → ℝ) (principalMultiplier : ι → ℕ → ℝ)
    (beta : ι → ℝ)
    (hupdate : IsTwoStepSquaredWeightUpdate exteriorWeight principalWeight
      exteriorMultiplier principalMultiplier)
    (k : ℕ) :
    logarithmicWeightCocycle exteriorWeight principalWeight beta (k + 2) -
        logarithmicWeightCocycle exteriorWeight principalWeight beta k =
      2 * Real.log (exteriorMultiplier k) +
        ∑ i, beta i * (2 * Real.log (principalMultiplier i k)) := by
  rw [logarithmicWeightCocycle_add_two_sub exteriorWeight principalWeight
    exteriorMultiplier principalMultiplier beta hupdate k]
  simp only [Real.log_pow, Nat.cast_ofNat]

/-- An eventually strictly increasing sequence has a fixed lower bound on a
tail. -/
theorem exists_eventual_lower_bound_of_eventually_lt_succ
    {Y : ℕ → ℝ} (hinc : ∀ᶠ k in atTop, Y k < Y (k + 1)) :
    ∃ K, ∀ k, K ≤ k → Y K ≤ Y k := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hinc
  refine ⟨K, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (hK k hk).le

/-- A sequence which is bounded below on a tail cannot tend to `atBot`. -/
theorem not_tendsto_atBot_of_eventually_ge_const
    {Y : ℕ → ℝ} {c : ℝ} (hlower : ∀ᶠ k in atTop, c ≤ Y k) :
    ¬Tendsto Y atTop atBot := by
  intro hbot
  have hupper : ∀ᶠ k in atTop, Y k ≤ c - 1 :=
    hbot (Iic_mem_atBot (c - 1))
  obtain ⟨k, hkLower, hkUpper⟩ := (hlower.and hupper).exists
  linarith

/-- An eventually strictly increasing sequence cannot tend to minus
infinity. -/
theorem not_tendsto_atBot_of_eventually_lt_succ
    {Y : ℕ → ℝ} (hinc : ∀ᶠ k in atTop, Y k < Y (k + 1)) :
    ¬Tendsto Y atTop atBot := by
  obtain ⟨K, hK⟩ :=
    exists_eventual_lower_bound_of_eventually_lt_succ hinc
  exact not_tendsto_atBot_of_eventually_ge_const
    (eventually_atTop.2 ⟨K, hK⟩)

/-- Nor can a cofinal subsequence of an eventually strictly increasing
sequence tend to minus infinity. -/
theorem not_tendsto_atBot_comp_of_eventually_lt_succ
    {Y : ℕ → ℝ} (hinc : ∀ᶠ k in atTop, Y k < Y (k + 1))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop) :
    ¬Tendsto (fun j => Y (phi j)) atTop atBot := by
  obtain ⟨K, hK⟩ :=
    exists_eventual_lower_bound_of_eventually_lt_succ hinc
  have hlower : ∀ᶠ j in atTop, Y K ≤ Y (phi j) :=
    hphi.eventually (eventually_atTop.2 ⟨K, hK⟩)
  exact not_tendsto_atBot_of_eventually_ge_const hlower

/-- Parity-specialized form used by the logarithmic cocycle argument. -/
theorem not_tendsto_parityCocycle_atBot_of_eventually_strictIncrease
    (Y : ℕ → ℝ) (r : ℕ)
    (hinc : ∀ᶠ k in atTop,
      Y (2 * k + r) < Y (2 * (k + 1) + r)) :
    ¬Tendsto (fun k => Y (2 * k + r)) atTop atBot :=
  not_tendsto_atBot_of_eventually_lt_succ hinc

/-- A cofinal subsequence of an eventually increasing parity cocycle cannot
tend to `atBot`. -/
theorem not_tendsto_parityCocycle_subsequence_atBot_of_eventually_strictIncrease
    (Y : ℕ → ℝ) (r : ℕ)
    (hinc : ∀ᶠ k in atTop,
      Y (2 * k + r) < Y (2 * (k + 1) + r))
    {phi : ℕ → ℕ} (hphi : Tendsto phi atTop atTop) :
    ¬Tendsto (fun j => Y (2 * phi j + r)) atTop atBot :=
  not_tendsto_atBot_comp_of_eventually_lt_succ hinc hphi

end

end Exterior
end Forsythe
