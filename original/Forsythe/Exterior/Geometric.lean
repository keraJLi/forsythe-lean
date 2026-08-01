import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Explicit geometric bounds for two-step contractions

Exterior spectral weights evolve independently on the two parities.  These
lemmas turn a uniform two-step contraction into explicit bounds, first for a
single nonnegative sequence and then for a finite total mass.
-/

set_option autoImplicit false

namespace Forsythe
namespace Exterior

open scoped BigOperators

/-- Iterating a nonnegative one-step contraction. -/
theorem le_mul_pow_of_step_le
    (u : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ n, u (n + 1) ≤ r * u n) :
    ∀ n, u n ≤ r ^ n * u 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        u (n + 1) ≤ r * u n := hstep n
        _ ≤ r * (r ^ n * u 0) := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (n + 1) * u 0 := by ring

/-- Explicit even-parity bound for a two-step contraction beginning at `K`. -/
theorem twoStep_even_le_mul_pow
    (u : ℕ → ℝ) (K : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ n, K ≤ n → u (n + 2) ≤ r * u n) :
    ∀ n, u (K + 2 * n) ≤ r ^ n * u K := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        u (K + 2 * (n + 1)) = u ((K + 2 * n) + 2) := by
          congr 1
        _ ≤ r * u (K + 2 * n) := hstep _ (by omega)
        _ ≤ r * (r ^ n * u K) := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (n + 1) * u K := by ring

/-- Explicit odd-parity bound for a two-step contraction beginning at `K`. -/
theorem twoStep_odd_le_mul_pow
    (u : ℕ → ℝ) (K : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ n, K ≤ n → u (n + 2) ≤ r * u n) :
    ∀ n, u (K + 2 * n + 1) ≤ r ^ n * u (K + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        u (K + 2 * (n + 1) + 1) = u ((K + 2 * n + 1) + 2) := by
          congr 1
        _ ≤ r * u (K + 2 * n + 1) := hstep _ (by omega)
        _ ≤ r * (r ^ n * u (K + 1)) := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (n + 1) * u (K + 1) := by ring

/-- Summing finitely many componentwise two-step contractions preserves the
same contraction factor. -/
theorem sum_twoStep_le
    {J : Type*} [Fintype J] (u : J → ℕ → ℝ)
    (K : ℕ) (r : ℝ)
    (hstep : ∀ j n, K ≤ n → u j (n + 2) ≤ r * u j n) :
    ∀ n, K ≤ n →
      ∑ j, u j (n + 2) ≤ r * ∑ j, u j n := by
  intro n hn
  calc
    ∑ j, u j (n + 2) ≤ ∑ j, r * u j n := by
      apply Finset.sum_le_sum
      intro j hj
      exact hstep j n hn
    _ = r * ∑ j, u j n := by rw [Finset.mul_sum]

/-- Uniform geometric bounds for the total mass on both parities. -/
theorem sum_twoStep_parity_geometric
    {J : Type*} [Fintype J] (u : J → ℕ → ℝ)
    (K : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ j n, K ≤ n → u j (n + 2) ≤ r * u j n) :
    (∀ n, ∑ j, u j (K + 2 * n) ≤ r ^ n * ∑ j, u j K) ∧
      (∀ n, ∑ j, u j (K + 2 * n + 1) ≤
        r ^ n * ∑ j, u j (K + 1)) := by
  let mass : ℕ → ℝ := fun n => ∑ j, u j n
  have hmass : ∀ n, K ≤ n → mass (n + 2) ≤ r * mass n :=
    sum_twoStep_le u K r hstep
  constructor
  · simpa only [mass] using twoStep_even_le_mul_pow mass K r hr hmass
  · simpa only [mass] using twoStep_odd_le_mul_pow mass K r hr hmass

end Exterior
end Forsythe
