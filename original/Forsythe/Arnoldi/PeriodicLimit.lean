import Forsythe.Arnoldi.Orbit

/-!
# Limits of an eventually two-periodic orbit

This module records the elementary terminal branch of the proof.  Once the
energy vanishes, the deterministic restart-two Arnoldi orbit is exactly
two-periodic on a tail, so each parity subsequence is eventually constant.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Topology

noncomputable section

/-- An eventually two-periodic sequence has convergent even and odd
subsequences. -/
theorem exists_tendsto_parities_of_eventually_twoPeriodic
    {X : Type*} [TopologicalSpace X] (u : ℕ → X) (K : ℕ)
    (hperiodic : ∀ n, K ≤ n → u (n + 2) = u n) :
    ∃ uEven uOdd,
      Tendsto (fun k ↦ u (2 * k)) atTop (𝓝 uEven) ∧
      Tendsto (fun k ↦ u (2 * k + 1)) atTop (𝓝 uOdd) := by
  have heven : ∀ k, K ≤ k → u (2 * k) = u (2 * K) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
        rw [show 2 * (k + 1) = 2 * k + 2 by omega,
          hperiodic (2 * k) (hk.trans (by omega)), ih]
  have hodd : ∀ k, K ≤ k → u (2 * k + 1) = u (2 * K + 1) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
          hperiodic (2 * k + 1) (hk.trans (by omega)), ih]
  refine ⟨u (2 * K), u (2 * K + 1), ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    exact eventually_atTop.2 ⟨K, fun k hk ↦ (heven k hk).symm⟩
  · apply tendsto_const_nhds.congr'
    exact eventually_atTop.2 ⟨K, fun k hk ↦ (hodd k hk).symm⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Operator-facing form of the eventual-periodicity branch. -/
theorem exists_tendsto_arnoldiOrbit2_parities_of_energy_eq_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) {K : ℕ}
    (henergy : quadraticStepEnergy A (arnoldiOrbit2 A v₀)
      (arnoldiFactorOrbit2 A v₀) (arnoldiNormalizerOrbit2 A v₀) K = 0) :
    ∃ vEven vOdd,
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))
        atTop (𝓝 vEven) ∧
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))
        atTop (𝓝 vOdd) := by
  exact exists_tendsto_parities_of_eventually_twoPeriodic
    (arnoldiOrbit2 A v₀) K
    (arnoldiOrbit2_eventually_two_periodic_of_energy_eq_zero
      A hA v₀ hv₀ hgrade₀ henergy)

/-- If the monotone Arnoldi height reaches its limiting value at a finite
index, the orbit is already in the exactly two-periodic branch. -/
theorem exists_tendsto_arnoldiOrbit2_parities_of_height_eq_limit
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ)
    (htau : Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (𝓝 tau))
    {K : ℕ}
    (hK : quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) K = tau ^ 2) :
    ∃ vEven vOdd,
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))
        atTop (𝓝 vEven) ∧
      Tendsto (fun k ↦ arnoldiOrbit2 A v₀ (2 * k + 1))
        atTop (𝓝 vOdd) := by
  let H : ℕ → ℝ :=
    quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀)
  have hH : Tendsto H atTop (𝓝 (tau ^ 2)) := by
    change Tendsto (fun k ↦ arnoldiNormalizerOrbit2 A v₀ k ^ 2)
      atTop (𝓝 (tau ^ 2))
    exact htau.pow 2
  have hmono : Monotone H := by
    simpa only [H] using
      arnoldiOrbit2_height_monotone A hA v₀ hv₀ hgrade₀
  have hnextLe : H (K + 1) ≤ tau ^ 2 := hmono.ge_of_tendsto hH (K + 1)
  have hheightEq : H (K + 1) = H K := by
    have hle := hmono (Nat.le_succ K)
    have hle' : H K ≤ H (K + 1) := by
      simpa only [Nat.succ_eq_add_one] using hle
    change H K = tau ^ 2 at hK
    linarith
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  have henergy : quadraticStepEnergy A (arnoldiOrbit2 A v₀)
      (arnoldiFactorOrbit2 A v₀) (arnoldiNormalizerOrbit2 A v₀) K = 0 :=
    (hsteps.energy_eq_zero_iff_height_eq hA K).2 (by
      simpa only [H] using hheightEq)
  exact exists_tendsto_arnoldiOrbit2_parities_of_energy_eq_zero
    A hA v₀ hv₀ hgrade₀ henergy

end

end Forsythe
