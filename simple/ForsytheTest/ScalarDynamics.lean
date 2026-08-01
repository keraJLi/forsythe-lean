import Forsythe.Dynamics.Scalar

/-! Compile-time regressions for both normalized scalar-recurrence branches. -/

set_option autoImplicit false

namespace ForsytheTest

open Filter Topology
open Forsythe.ScalarDynamics

private def oneMultiplier : ℕ → ℝ := fun _ ↦ 1
private def zeroForcing : ℕ → ℝ := fun _ ↦ 0
private def zeroSolution : ℕ → ℝ := fun _ ↦ 0
private def oneSolution : ℕ → ℝ := fun _ ↦ 1

private theorem zeroDichotomy : ∃ L : ℝ,
    Tendsto (fun k ↦ zeroSolution k / normalizedProduct oneMultiplier k)
      atTop (𝓝 L) ∧
    ((L = 0 ∧
        (∀ k, zeroSolution k = -normalizedProduct oneMultiplier k *
          ∑' j, zeroForcing (j + k) /
            normalizedProduct oneMultiplier (j + k + 1)) ∧
        ∃ C' : ℝ, 0 ≤ C' ∧
          ∀ᶠ k in atTop, |zeroSolution k| ≤ C' * (1 / 2 : ℝ) ^ k) ∨
      (L ≠ 0 ∧ (∀ᶠ k in atTop, 0 < L * zeroSolution k) ∧
        Tendsto (fun k ↦ (1 / 2 : ℝ) ^ k / |zeroSolution k|)
          atTop (𝓝 0))) := by
  apply normalizedRecurrence_geometric_dichotomy
    (alpha := zeroSolution) (m := oneMultiplier) (b := zeroForcing)
    (C := 0) (theta := (1 : ℝ) / 2)
  · intro k
    norm_num [oneMultiplier]
  · change Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)
    exact tendsto_const_nhds
  · intro k
    simp [zeroSolution, oneMultiplier, zeroForcing]
  · norm_num
  · norm_num
  · norm_num
  · intro k
    norm_num [zeroForcing]

private theorem oneDichotomy : ∃ L : ℝ,
    Tendsto (fun k ↦ oneSolution k / normalizedProduct oneMultiplier k)
      atTop (𝓝 L) ∧
    ((L = 0 ∧
        (∀ k, oneSolution k = -normalizedProduct oneMultiplier k *
          ∑' j, zeroForcing (j + k) /
            normalizedProduct oneMultiplier (j + k + 1)) ∧
        ∃ C' : ℝ, 0 ≤ C' ∧
          ∀ᶠ k in atTop, |oneSolution k| ≤ C' * (1 / 2 : ℝ) ^ k) ∨
      (L ≠ 0 ∧ (∀ᶠ k in atTop, 0 < L * oneSolution k) ∧
        Tendsto (fun k ↦ (1 / 2 : ℝ) ^ k / |oneSolution k|)
          atTop (𝓝 0))) := by
  apply normalizedRecurrence_geometric_dichotomy
    (alpha := oneSolution) (m := oneMultiplier) (b := zeroForcing)
    (C := 0) (theta := (1 : ℝ) / 2)
  · intro k
    norm_num [oneMultiplier]
  · change Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)
    exact tendsto_const_nhds
  · intro k
    simp [oneSolution, oneMultiplier, zeroForcing]
  · norm_num
  · norm_num
  · norm_num
  · intro k
    norm_num [zeroForcing]

/-- The zero normalized limit really selects the geometric-decay branch of
the dichotomy, rather than merely satisfying its disjunctive conclusion. -/
example : ∃ L : ℝ,
    Tendsto (fun k ↦ zeroSolution k / normalizedProduct oneMultiplier k)
      atTop (𝓝 L) ∧
    L = 0 ∧
    (∀ k, zeroSolution k = -normalizedProduct oneMultiplier k *
      ∑' j, zeroForcing (j + k) /
        normalizedProduct oneMultiplier (j + k + 1)) ∧
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ᶠ k in atTop, |zeroSolution k| ≤ C' * (1 / 2 : ℝ) ^ k := by
  obtain ⟨L, hL, hcase⟩ := zeroDichotomy
  have hLzero : L = 0 := by
    apply tendsto_nhds_unique hL
    simp [zeroSolution]
  rcases hcase with hzero | hnonzero
  · exact ⟨L, hL, hzero⟩
  · exact (hnonzero.1 hLzero).elim

/-- The nonzero normalized limit really selects the eventually one-signed,
forcing-negligible branch of the dichotomy. -/
example : ∃ L : ℝ,
    Tendsto (fun k ↦ oneSolution k / normalizedProduct oneMultiplier k)
      atTop (𝓝 L) ∧
    L ≠ 0 ∧
    (∀ᶠ k in atTop, 0 < L * oneSolution k) ∧
    Tendsto (fun k ↦ (1 / 2 : ℝ) ^ k / |oneSolution k|)
      atTop (𝓝 0) := by
  obtain ⟨L, hL, hcase⟩ := oneDichotomy
  have hLone : L = 1 := by
    apply tendsto_nhds_unique hL
    simp [oneSolution, oneMultiplier, normalizedProduct]
  rcases hcase with hzero | hnonzero
  · exact (by linarith [hzero.1, hLone] : False).elim
  · exact ⟨L, hL, hnonzero⟩

end ForsytheTest
