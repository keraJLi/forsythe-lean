import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

/-!
# Convergence on an eventually fixed positive ray

This generic lemma is the final sign-recovery step in the spectral proof.  If
successive vectors are positive scalar multiples on a tail, convergence of
their norms already implies convergence of the vectors themselves.
-/

set_option autoImplicit false

namespace Forsythe
namespace Dynamics

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive scalar recurrences fix a ray; a convergent norm then determines
the vector limit on that ray. -/
theorem exists_tendsto_of_positive_smul_and_norm_tendsto
    (u : ℕ → E) (m : ℕ → ℝ) (K : ℕ) (r : ℝ)
    (hrec : ∀ n, K ≤ n → u (n + 1) = m n • u n)
    (hm : ∀ n, K ≤ n → 0 < m n)
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 r)) :
    ∃ uLim : E, Tendsto u atTop (𝓝 uLim) := by
  by_cases hzero : u K = 0
  · have htail : ∀ n, K ≤ n → u n = 0 := by
      intro n hKn
      induction n, hKn using Nat.le_induction with
      | base => exact hzero
      | succ n hn ih => rw [hrec n hn, ih, smul_zero]
    have heq : u =ᶠ[atTop] fun _ => (0 : E) :=
      eventually_atTop.2 ⟨K, htail⟩
    exact ⟨0, tendsto_const_nhds.congr' heq.symm⟩
  · have hnormK : 0 < ‖u K‖ := (norm_pos_iff.mpr hzero)
    let direction : E := ‖u K‖⁻¹ • u K
    have htail : ∀ n, K ≤ n → u n = ‖u n‖ • direction := by
      intro n hKn
      induction n, hKn using Nat.le_induction with
      | base =>
          simp [direction, smul_smul, ne_of_gt hnormK]
      | succ n hn ih =>
          have hmPos := hm n hn
          have hnormSucc : ‖u (n + 1)‖ = m n * ‖u n‖ := by
            rw [hrec n hn, norm_smul, Real.norm_eq_abs, abs_of_pos hmPos]
          calc
            u (n + 1) = m n • u n := hrec n hn
            _ = m n • (‖u n‖ • direction) :=
              congrArg (fun x : E => m n • x) ih
            _ = (m n * ‖u n‖) • direction := by rw [smul_smul]
            _ = ‖u (n + 1)‖ • direction := by rw [hnormSucc]
    have heq : u =ᶠ[atTop] fun n => ‖u n‖ • direction :=
      eventually_atTop.2 ⟨K, htail⟩
    exact ⟨r • direction, (hnorm.smul_const direction).congr' heq.symm⟩

/-- Filter-style wrapper: eventual positivity and recurrence suffice. -/
theorem exists_tendsto_of_eventually_positive_smul_and_norm_tendsto
    (u : ℕ → E) (m : ℕ → ℝ) (r : ℝ)
    (hrec : ∀ᶠ n in atTop, u (n + 1) = m n • u n)
    (hm : ∀ᶠ n in atTop, 0 < m n)
    (hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 r)) :
    ∃ uLim : E, Tendsto u atTop (𝓝 uLim) := by
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 hrec
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 hm
  let K := max K₁ K₂
  exact exists_tendsto_of_positive_smul_and_norm_tendsto u m K r
    (fun n hn => hK₁ n ((le_max_left K₁ K₂).trans hn))
    (fun n hn => hK₂ n ((le_max_right K₁ K₂).trans hn)) hnorm

end Dynamics
end Forsythe
