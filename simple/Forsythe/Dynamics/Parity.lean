import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Basic

/-!
# Recombining even and odd tails

Elementary filter lemmas used when two parity subsequences satisfy the same
eventual property or converge to the same limit.
-/

set_option autoImplicit false

namespace Forsythe

open Filter

/-- Eventual properties on both parity subsequences recombine to an eventual
property on the original natural-number sequence. -/
theorem eventually_of_even_odd
    {P : ℕ → Prop}
    (heven : ∀ᶠ k in atTop, P (2 * k))
    (hodd : ∀ᶠ k in atTop, P (2 * k + 1)) :
    ∀ᶠ n in atTop, P n := by
  obtain ⟨Ke, hKe⟩ := eventually_atTop.1 heven
  obtain ⟨Ko, hKo⟩ := eventually_atTop.1 hodd
  refine eventually_atTop.2 ⟨2 * max Ke Ko, ?_⟩
  intro n hn
  obtain ⟨k, hk | hk⟩ := n.even_or_odd'
  · rw [hk] at hn ⊢
    exact hKe k (by omega)
  · rw [hk] at hn ⊢
    exact hKo k (by omega)

/-- If both parity subsequences converge to the same point, then the full
sequence converges to that point. -/
theorem tendsto_of_even_odd
    {X : Type*} {u : ℕ → X} {l : Filter X}
    (heven : Tendsto (fun k ↦ u (2 * k)) atTop l)
    (hodd : Tendsto (fun k ↦ u (2 * k + 1)) atTop l) :
    Tendsto u atTop l := by
  intro s hs
  exact eventually_of_even_odd (heven hs) (hodd hs)

end Forsythe
