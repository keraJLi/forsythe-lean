import Forsythe.Arnoldi.Variation
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Convergence from factor variation

This module contains the analytic tail of the factor-variation argument.  It
does not depend on the origin of the factors: a summable nonnegative height
increment and the uniform estimate

`coeffDist (P (k + 2)) (P k) ≤ C * (H (k + 1) - H k)`

force both parity subsequences of the two free coefficients to converge.  If
`H k → H∞`, the same proof gives the concrete product-norm tail estimate

`coeffDist (P (2n + r)) pᵣ ≤ C * (H∞ - H (2n + r))`.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Topology

noncomputable section

namespace MonicQuadratic

/-- Reconstruct a monic quadratic from its two free coefficients. -/
def ofCoeffPair (c : ℝ × ℝ) : MonicQuadratic :=
  ⟨c.1, c.2⟩

@[simp]
theorem coeffPair_ofCoeffPair (c : ℝ × ℝ) :
    (ofCoeffPair c).coeffPair = c := by
  cases c
  rfl

@[simp]
theorem ofCoeffPair_coeffPair (p : MonicQuadratic) :
    ofCoeffPair p.coeffPair = p := by
  cases p
  rfl

end MonicQuadratic

namespace Arnoldi

/-- The height increment used in the factor-variation estimate. -/
def heightIncrement (H : ℕ → ℝ) (k : ℕ) : ℝ :=
  H (k + 1) - H k

/-- A uniform factor-variation estimate, stated in the fixed product norm on
the two free coefficients. -/
def HasFactorVariation (P : ℕ → MonicQuadratic) (H : ℕ → ℝ)
    (C : ℝ) : Prop :=
  ∀ k, (P (k + 2)).coeffDist (P k) ≤ C * heightIncrement H k

private theorem parityIndex_injective (r : ℕ) :
    Function.Injective (fun n : ℕ ↦ 2 * n + r) := by
  intro m n h
  have hmul : 2 * m = 2 * n := Nat.add_right_cancel h
  omega

private theorem parityIndex_succ (n r : ℕ) :
    2 * (n + 1) + r = (2 * n + r) + 2 := by
  omega

/-- Restricting a summable sequence to either parity preserves summability. -/
theorem summable_comp_parity {a : ℕ → ℝ} (ha : Summable a) (r : ℕ) :
    Summable (fun n ↦ a (2 * n + r)) :=
  ha.comp_injective (parityIndex_injective r)

/-- Factor variation makes the product-norm distances between consecutive
members of any fixed-parity coefficient sequence summable. -/
theorem summable_parity_coeffPair_dist
    (P : ℕ → MonicQuadratic) (H : ℕ → ℝ) (C : ℝ)
    (hvariation : HasFactorVariation P H C)
    (hsum : Summable (heightIncrement H)) (r : ℕ) :
    Summable (fun n ↦
      dist (P (2 * n + r)).coeffPair (P (2 * (n + 1) + r)).coeffPair) := by
  have hbound : ∀ n : ℕ,
      dist (P (2 * n + r)).coeffPair (P (2 * (n + 1) + r)).coeffPair ≤
        C * heightIncrement H (2 * n + r) := by
    intro n
    rw [dist_comm, parityIndex_succ]
    simpa only [MonicQuadratic.coeffDist, dist_eq_norm] using
      hvariation (2 * n + r)
  exact ((summable_comp_parity hsum r).mul_left C).of_nonneg_of_le
    (fun n ↦ dist_nonneg) hbound

/-- Each parity subsequence of coefficient pairs is Cauchy. -/
theorem cauchySeq_parity_coeffPair
    (P : ℕ → MonicQuadratic) (H : ℕ → ℝ) (C : ℝ)
    (hvariation : HasFactorVariation P H C)
    (hsum : Summable (heightIncrement H)) (r : ℕ) :
    CauchySeq (fun n ↦ (P (2 * n + r)).coeffPair) :=
  cauchySeq_of_summable_dist <|
    summable_parity_coeffPair_dist P H C hvariation hsum r

/-- A fixed parity of monic factors converges coefficientwise. -/
theorem exists_parity_factor_limit
    (P : ℕ → MonicQuadratic) (H : ℕ → ℝ) (C : ℝ)
    (hvariation : HasFactorVariation P H C)
    (hsum : Summable (heightIncrement H)) (r : ℕ) :
    ∃ pLim : MonicQuadratic,
      Tendsto (fun n ↦ (P (2 * n + r)).coeffPair) atTop (nhds pLim.coeffPair) := by
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_parity_coeffPair P H C hvariation hsum r)
  exact ⟨MonicQuadratic.ofCoeffPair c, by simpa using hc⟩

/-- The even and odd monic factors converge coefficientwise. -/
theorem exists_paritywise_factor_limits
    (P : ℕ → MonicQuadratic) (H : ℕ → ℝ) (C : ℝ)
    (hvariation : HasFactorVariation P H C)
    (hsum : Summable (heightIncrement H)) :
    ∃ pEven pOdd : MonicQuadratic,
      Tendsto (fun n ↦ (P (2 * n)).coeffPair) atTop (nhds pEven.coeffPair) ∧
      Tendsto (fun n ↦ (P (2 * n + 1)).coeffPair) atTop (nhds pOdd.coeffPair) := by
  obtain ⟨pEven, hpEven⟩ :=
    exists_parity_factor_limit P H C hvariation hsum 0
  obtain ⟨pOdd, hpOdd⟩ :=
    exists_parity_factor_limit P H C hvariation hsum 1
  simpa only [Nat.add_zero] using ⟨pEven, pOdd, hpEven, hpOdd⟩

private theorem sum_heightIncrement_tail (H : ℕ → ℝ) (k n : ℕ) :
    ∑ j ∈ Finset.range n, heightIncrement H (k + j) = H (k + n) - H k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [heightIncrement]
      ring_nf

/-- The increments on a tail telescope to the remaining distance from the
height limit. -/
theorem hasSum_heightIncrement_tail
    (H : ℕ → ℝ) (Hlim : ℝ)
    (hinc : ∀ k, 0 ≤ heightIncrement H k)
    (hH : Tendsto H atTop (nhds Hlim)) (k : ℕ) :
    HasSum (fun n ↦ heightIncrement H (k + n)) (Hlim - H k) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ hinc (k + n))]
  have htail : Tendsto (fun n ↦ H (k + n) - H k) atTop (nhds (Hlim - H k)) := by
    have hshift : Tendsto (fun n ↦ H (n + k)) atTop (nhds Hlim) :=
      hH.comp (tendsto_add_atTop_nat k)
    convert hshift.sub tendsto_const_nhds using 1; simp only [add_comm]
  convert htail using 1
  exact funext (sum_heightIncrement_tail H k)

private theorem summable_scaled_parity_tail
    (H : ℕ → ℝ) (C : ℝ)
    (hsum : Summable (heightIncrement H)) (n r : ℕ) :
    Summable (fun j ↦ C * heightIncrement H (2 * (n + j) + r)) := by
  have hparity : Summable (fun m ↦ heightIncrement H (2 * m + r)) :=
    summable_comp_parity hsum r
  have hshift : Summable (fun j ↦ heightIncrement H (2 * (j + n) + r)) :=
    hparity.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  simpa only [add_comm n] using hshift.mul_left C

/-- Quantitative coefficient tail bound in terms of the selected-parity
increment series. -/
theorem coeffDist_le_parity_increment_tsum
    (P : ℕ → MonicQuadratic) (H : ℕ → ℝ) (C : ℝ)
    (hvariation : HasFactorVariation P H C)
    (hsum : Summable (heightIncrement H))
    (r : ℕ) (pLim : MonicQuadratic)
    (hlim : Tendsto (fun n ↦ (P (2 * n + r)).coeffPair)
      atTop (nhds pLim.coeffPair)) (n : ℕ) :
    (P (2 * n + r)).coeffDist pLim ≤
      ∑' j, C * heightIncrement H (2 * (n + j) + r) := by
  let f : ℕ → ℝ × ℝ := fun m ↦ (P (2 * m + r)).coeffPair
  let d : ℕ → ℝ := fun m ↦ C * heightIncrement H (2 * m + r)
  have hdist : ∀ m, dist (f m) (f (m + 1)) ≤ d m := by
    intro m
    dsimp only [f, d]
    rw [dist_comm, parityIndex_succ]
    simpa only [MonicQuadratic.coeffDist, dist_eq_norm] using
      hvariation (2 * m + r)
  have hdsum : Summable d := (summable_comp_parity hsum r).mul_left C
  have htail := dist_le_tsum_of_dist_le_of_tendsto d hdist hdsum hlim n
  simpa only [f, d, MonicQuadratic.coeffDist, dist_eq_norm] using htail

/-- A selected-parity increment tail is bounded by the full telescoping
height tail. -/
theorem parity_increment_tsum_le_height_tail
    (H : ℕ → ℝ) (Hlim C : ℝ)
    (hC : 0 ≤ C)
    (hinc : ∀ k, 0 ≤ heightIncrement H k)
    (hsum : Summable (heightIncrement H))
    (hH : Tendsto H atTop (nhds Hlim)) (n r : ℕ) :
    ∑' j, C * heightIncrement H (2 * (n + j) + r) ≤
      C * (Hlim - H (2 * n + r)) := by
  let k := 2 * n + r
  let selected : ℕ → ℝ :=
    fun j ↦ C * heightIncrement H (2 * (n + j) + r)
  let full : ℕ → ℝ := fun j ↦ C * heightIncrement H (k + j)
  have hselected : Summable selected := by
    simpa only [selected] using summable_scaled_parity_tail H C hsum n r
  have hfullHasSum : HasSum full (C * (Hlim - H k)) := by
    simpa only [full] using (hasSum_heightIncrement_tail H Hlim hinc hH k).mul_left C
  have hle : ∑' j, selected j ≤ ∑' j, full j := by
    apply hselected.tsum_le_tsum_of_inj (fun j : ℕ ↦ 2 * j)
      (by
        intro a b hab
        exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hab)
    · intro j _
      exact mul_nonneg hC (hinc (k + j))
    · intro j
      dsimp only [selected, full, k]
      rw [show 2 * (n + j) + r = 2 * n + r + 2 * j by omega]
    · exact hfullHasSum.summable
  simpa only [selected, hfullHasSum.tsum_eq, k] using hle

/-- Explicit product-norm coefficient tail estimate for a convergent parity
of factors. -/
theorem coeffDist_parity_limit_le_height_tail
    (P : ℕ → MonicQuadratic) (H : ℕ → ℝ) (Hlim C : ℝ)
    (hC : 0 ≤ C)
    (hinc : ∀ k, 0 ≤ heightIncrement H k)
    (hsum : Summable (heightIncrement H))
    (hH : Tendsto H atTop (nhds Hlim))
    (hvariation : HasFactorVariation P H C)
    (r : ℕ) (pLim : MonicQuadratic)
    (hlim : Tendsto (fun n ↦ (P (2 * n + r)).coeffPair)
      atTop (nhds pLim.coeffPair)) (n : ℕ) :
    (P (2 * n + r)).coeffDist pLim ≤
      C * (Hlim - H (2 * n + r)) :=
  (coeffDist_le_parity_increment_tsum P H C hvariation hsum r pLim hlim n).trans
    (parity_increment_tsum_le_height_tail H Hlim C hC hinc hsum hH n r)

/-- Both parity limits, together with their explicit coefficient-tail
bounds. -/
theorem exists_paritywise_factor_limits_with_tail
    (P : ℕ → MonicQuadratic) (H : ℕ → ℝ) (Hlim C : ℝ)
    (hC : 0 ≤ C)
    (hinc : ∀ k, 0 ≤ heightIncrement H k)
    (hsum : Summable (heightIncrement H))
    (hH : Tendsto H atTop (nhds Hlim))
    (hvariation : HasFactorVariation P H C) :
    ∃ pEven pOdd : MonicQuadratic,
      Tendsto (fun n ↦ (P (2 * n)).coeffPair) atTop (nhds pEven.coeffPair) ∧
      Tendsto (fun n ↦ (P (2 * n + 1)).coeffPair) atTop (nhds pOdd.coeffPair) ∧
      (∀ n, (P (2 * n)).coeffDist pEven ≤ C * (Hlim - H (2 * n))) ∧
      (∀ n, (P (2 * n + 1)).coeffDist pOdd ≤
        C * (Hlim - H (2 * n + 1))) := by
  obtain ⟨pEven, pOdd, hpEven, hpOdd⟩ :=
    exists_paritywise_factor_limits P H C hvariation hsum
  refine ⟨pEven, pOdd, hpEven, hpOdd, ?_, ?_⟩
  · intro n
    simpa only [Nat.add_zero] using
      coeffDist_parity_limit_le_height_tail P H Hlim C hC hinc hsum hH
        hvariation 0 pEven (by simpa only [Nat.add_zero] using hpEven) n
  · intro n
    exact coeffDist_parity_limit_le_height_tail P H Hlim C hC hinc hsum hH
      hvariation 1 pOdd hpOdd n

end Arnoldi

end
end Forsythe
