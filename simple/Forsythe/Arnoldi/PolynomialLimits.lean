import Forsythe.Arnoldi.Asymptotics
import Forsythe.Arnoldi.OrbitVariation

/-!
# Polynomial limits along the Arnoldi orbit

The uniform tail variation estimate is shifted past its coercivity threshold,
combined with the summable height increments, and then shifted back.  This
produces the manuscript's even and odd limiting monic quadratics.  We also
use a concrete four-coefficient product norm for the two-step products.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace Arnoldi

/-- The four free coefficients `(X³,X²,X,1)` of the product of two monic
quadratics, stored in a nested product with its concrete max norm. -/
def quadraticProductCoeff (p q : MonicQuadratic) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  ((p.linearCoeff + q.linearCoeff,
      p.constantCoeff + q.constantCoeff + p.linearCoeff * q.linearCoeff),
    (p.linearCoeff * q.constantCoeff + p.constantCoeff * q.linearCoeff,
      p.constantCoeff * q.constantCoeff))

theorem quadraticProductCoeff_comm (p q : MonicQuadratic) :
    quadraticProductCoeff p q = quadraticProductCoeff q p := by
  ext <;> dsimp only [quadraticProductCoeff] <;> ring

/-- Coefficientwise convergence of both factors implies convergence of their
concrete four-coefficient product. -/
theorem tendsto_quadraticProductCoeff
    {P Q : ℕ → MonicQuadratic} {p q : MonicQuadratic}
    (hP : Tendsto (fun n ↦ (P n).coeffPair) atTop (nhds p.coeffPair))
    (hQ : Tendsto (fun n ↦ (Q n).coeffPair) atTop (nhds q.coeffPair)) :
    Tendsto (fun n ↦ quadraticProductCoeff (P n) (Q n)) atTop
      (nhds (quadraticProductCoeff p q)) := by
  have hPa : Tendsto (fun n ↦ (P n).linearCoeff) atTop
      (nhds p.linearCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hP.fst_nhds
  have hPb : Tendsto (fun n ↦ (P n).constantCoeff) atTop
      (nhds p.constantCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hP.snd_nhds
  have hQa : Tendsto (fun n ↦ (Q n).linearCoeff) atTop
      (nhds q.linearCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hQ.fst_nhds
  have hQb : Tendsto (fun n ↦ (Q n).constantCoeff) atTop
      (nhds q.constantCoeff) := by
    simpa only [MonicQuadratic.coeffPair] using hQ.snd_nhds
  dsimp only [quadraticProductCoeff]
  exact Tendsto.prodMk_nhds
    (Tendsto.prodMk_nhds (hPa.add hQa)
      ((hPb.add hQb).add (hPa.mul hQa)))
    (Tendsto.prodMk_nhds ((hPa.mul hQb).add (hPb.mul hQa))
      (hPb.mul hQb))

/-- Multiplication by a quadratic with coefficient norm at most `M` is
Lipschitz on the other factor's free coefficients. -/
theorem quadraticProductCoeff_dist_le
    (p q r : MonicQuadratic) {M : ℝ} (hM : 0 ≤ M)
    (hr : ‖r.coeffPair‖ ≤ M) :
    dist (quadraticProductCoeff p r) (quadraticProductCoeff q r) ≤
      (1 + 2 * M) * p.coeffDist q := by
  let da := p.linearCoeff - q.linearCoeff
  let db := p.constantCoeff - q.constantCoeff
  let d := p.coeffDist q
  have hda : |da| ≤ d := by
    dsimp only [da, d, MonicQuadratic.coeffDist, MonicQuadratic.coeffPair,
      Prod.norm_def]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_left _ _
  have hdb : |db| ≤ d := by
    dsimp only [db, d, MonicQuadratic.coeffDist, MonicQuadratic.coeffPair,
      Prod.norm_def]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_right _ _
  have hrc : |r.linearCoeff| ≤ M :=
    (r.abs_linearCoeff_le_coeffPair_norm).trans hr
  have hrd : |r.constantCoeff| ≤ M :=
    (r.abs_constantCoeff_le_coeffPair_norm).trans hr
  have hdnonneg : 0 ≤ d := MonicQuadratic.coeffDist_nonneg _ _
  have hLnonneg : 0 ≤ 1 + 2 * M := by linarith
  rw [dist_eq_norm]
  change max
      (max
        |(p.linearCoeff + r.linearCoeff) - (q.linearCoeff + r.linearCoeff)|
        |(p.constantCoeff + r.constantCoeff + p.linearCoeff * r.linearCoeff) -
          (q.constantCoeff + r.constantCoeff + q.linearCoeff * r.linearCoeff)|)
      (max
        |(p.linearCoeff * r.constantCoeff + p.constantCoeff * r.linearCoeff) -
          (q.linearCoeff * r.constantCoeff + q.constantCoeff * r.linearCoeff)|
        |p.constantCoeff * r.constantCoeff - q.constantCoeff * r.constantCoeff|) ≤
    (1 + 2 * M) * p.coeffDist q
  apply max_le
  · apply max_le
    ·
      rw [show p.linearCoeff + r.linearCoeff - (q.linearCoeff + r.linearCoeff) = da by
        dsimp only [da]; ring]
      nlinarith
    ·
      rw [show
        p.constantCoeff + r.constantCoeff + p.linearCoeff * r.linearCoeff -
            (q.constantCoeff + r.constantCoeff + q.linearCoeff * r.linearCoeff) =
          db + da * r.linearCoeff by
        dsimp only [da, db]; ring]
      calc
        |db + da * r.linearCoeff| ≤ |db| + |da * r.linearCoeff| := abs_add_le _ _
        _ = |db| + |da| * |r.linearCoeff| := by rw [abs_mul]
        _ ≤ d + d * M := by gcongr
        _ ≤ (1 + 2 * M) * d := by nlinarith
  · apply max_le
    ·
      rw [show
        p.linearCoeff * r.constantCoeff + p.constantCoeff * r.linearCoeff -
            (q.linearCoeff * r.constantCoeff + q.constantCoeff * r.linearCoeff) =
          da * r.constantCoeff + db * r.linearCoeff by
        dsimp only [da, db]; ring]
      calc
        |da * r.constantCoeff + db * r.linearCoeff| ≤
            |da * r.constantCoeff| + |db * r.linearCoeff| := abs_add_le _ _
        _ = |da| * |r.constantCoeff| + |db| * |r.linearCoeff| := by
          rw [abs_mul, abs_mul]
        _ ≤ d * M + d * M := by gcongr
        _ ≤ (1 + 2 * M) * d := by nlinarith
    ·
      rw [show p.constantCoeff * r.constantCoeff -
          q.constantCoeff * r.constantCoeff = db * r.constantCoeff by
        dsimp only [db]; ring, abs_mul]
      calc
        |db| * |r.constantCoeff| ≤ d * M := by gcongr
        _ ≤ (1 + 2 * M) * d := by nlinarith

private theorem summable_heightIncrement_shift {H : ℕ → ℝ}
    (h : Summable (heightIncrement H)) (K : ℕ) :
    Summable (heightIncrement (fun n ↦ H (n + K))) := by
  have hs : Summable (fun n ↦ heightIncrement H (n + K)) :=
    h.comp_injective (i := fun n : ℕ ↦ n + K)
      (fun _ _ hEq ↦ Nat.add_right_cancel hEq)
  change Summable (fun n ↦ H ((n + 1) + K) - H (n + K))
  simpa only [heightIncrement, Nat.add_assoc, Nat.add_comm K 1] using hs

/-- The two parity subsequences of the Arnoldi factors converge
coefficientwise, with no tail shift left in the public statement. -/
theorem exists_arnoldiOrbit2_factor_limits
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ pEven pOdd : MonicQuadratic,
      Tendsto (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
        atTop (nhds pEven.coeffPair) ∧
      Tendsto (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
        atTop (nhds pOdd.coeffPair) := by
  let P := arnoldiFactorOrbit2 A v₀
  let H := arnoldiHeightOrbit2 A v₀
  obtain ⟨K, C, _, hvariation⟩ :=
    exists_shifted_arnoldiOrbit2_hasFactorVariation A hA v₀ hv₀ hgrade₀
  have hsum : Summable (heightIncrement H) := by
    change Summable (fun k ↦
      quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) (k + 1) -
        quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) k)
    exact summable_arnoldiOrbit2_height_increment_of_initial_grade_three
      A hA v₀ hv₀ hgrade₀
  have hsumShift : Summable (heightIncrement (fun n ↦ H (n + K))) :=
    summable_heightIncrement_shift hsum K
  obtain ⟨p₀, p₁, hp₀, hp₁⟩ := exists_paritywise_factor_limits
    (fun n ↦ P (n + K)) (fun n ↦ H (n + K)) C hvariation hsumShift
  rcases Nat.even_or_odd' K with ⟨m, hK | hK⟩
  · subst K
    have hpEvenShift : Tendsto (fun n ↦ (P (2 * (n + m))).coeffPair)
        atTop (nhds p₀.coeffPair) := by
      have heq : (fun n ↦ (P (2 * (n + m))).coeffPair) =
          (fun n ↦ (P (2 * n + 2 * m)).coeffPair) := by
        funext n
        rw [show 2 * (n + m) = 2 * n + 2 * m by omega]
      rw [heq]
      exact hp₀
    have hpOddShift : Tendsto (fun n ↦ (P (2 * (n + m) + 1)).coeffPair)
        atTop (nhds p₁.coeffPair) := by
      have heq : (fun n ↦ (P (2 * (n + m) + 1)).coeffPair) =
          (fun n ↦ (P (2 * n + 1 + 2 * m)).coeffPair) := by
        funext n
        rw [show 2 * (n + m) + 1 = 2 * n + 1 + 2 * m by omega]
      rw [heq]
      exact hp₁
    refine ⟨p₀, p₁, ?_, ?_⟩
    · exact (tendsto_add_atTop_iff_nat (f := fun n ↦ (P (2 * n)).coeffPair) m).mp
        (by simpa only using hpEvenShift)
    · exact (tendsto_add_atTop_iff_nat
        (f := fun n ↦ (P (2 * n + 1)).coeffPair) m).mp
          (by simpa only using hpOddShift)
  · subst K
    have hpOddShift : Tendsto (fun n ↦ (P (2 * (n + m) + 1)).coeffPair)
        atTop (nhds p₀.coeffPair) := by
      have heq : (fun n ↦ (P (2 * (n + m) + 1)).coeffPair) =
          (fun n ↦ (P (2 * n + (2 * m + 1))).coeffPair) := by
        funext n
        rw [show 2 * (n + m) + 1 = 2 * n + (2 * m + 1) by omega]
      rw [heq]
      exact hp₀
    have hpEvenShift : Tendsto (fun n ↦ (P (2 * (n + (m + 1)))).coeffPair)
        atTop (nhds p₁.coeffPair) := by
      have heq : (fun n ↦ (P (2 * (n + (m + 1)))).coeffPair) =
          (fun n ↦ (P (2 * n + 1 + (2 * m + 1))).coeffPair) := by
        funext n
        rw [show 2 * (n + (m + 1)) = 2 * n + 1 + (2 * m + 1) by omega]
      rw [heq]
      exact hp₁
    refine ⟨p₁, p₀, ?_, ?_⟩
    · exact (tendsto_add_atTop_iff_nat
        (f := fun n ↦ (P (2 * n)).coeffPair) (m + 1)).mp
          (by simpa only using hpEvenShift)
    · exact (tendsto_add_atTop_iff_nat
        (f := fun n ↦ (P (2 * n + 1)).coeffPair) m).mp
          (by simpa only using hpOddShift)

private theorem tendsto_two_mul :
    Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  exact eventually_atTop.2 ⟨N, fun n hn ↦ by omega⟩

/-- A shared bounded quadratic factor converts factor variation into
variation of the concrete four-coefficient product. -/
theorem quadraticProductCoeff_succ_dist_le
    (P : ℕ → MonicQuadratic) (H : ℕ → ℝ) {C M : ℝ}
    (_hC : 0 ≤ C) (hM : 0 ≤ M) {k : ℕ}
    (hvariation : (P (k + 2)).coeffDist (P k) ≤ C * heightIncrement H k)
    (hbound : ‖(P (k + 1)).coeffPair‖ ≤ M) :
    dist (quadraticProductCoeff (P k) (P (k + 1)))
        (quadraticProductCoeff (P (k + 1)) (P (k + 2))) ≤
      ((1 + 2 * M) * C) * heightIncrement H k := by
  rw [quadraticProductCoeff_comm (P (k + 1)) (P (k + 2))]
  calc
    dist (quadraticProductCoeff (P k) (P (k + 1)))
        (quadraticProductCoeff (P (k + 2)) (P (k + 1))) =
        dist (quadraticProductCoeff (P (k + 2)) (P (k + 1)))
          (quadraticProductCoeff (P k) (P (k + 1))) := dist_comm _ _
    _ ≤ (1 + 2 * M) * (P (k + 2)).coeffDist (P k) :=
      quadraticProductCoeff_dist_le (P (k + 2)) (P k) (P (k + 1)) hM hbound
    _ ≤ ((1 + 2 * M) * C) * heightIncrement H k := by
      have hL : 0 ≤ 1 + 2 * M := by linarith
      calc
        (1 + 2 * M) * (P (k + 2)).coeffDist (P k) ≤
            (1 + 2 * M) * (C * heightIncrement H k) :=
          mul_le_mul_of_nonneg_left hvariation hL
        _ = ((1 + 2 * M) * C) * heightIncrement H k := by ring

/-- The eventual Cramer bound can be enlarged over its finite prefix to give
a single coefficient bound for every Arnoldi factor. -/
private theorem exists_global_arnoldiFactorOrbit2_coeffPair_bound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ k, ‖(arnoldiFactorOrbit2 A v₀ k).coeffPair‖ ≤ M := by
  let P := arnoldiFactorOrbit2 A v₀
  obtain ⟨Mtail, hMtail, hboundEventually⟩ :=
    exists_eventually_arnoldiFactorOrbit2_coeffPair_bound
      A hA v₀ hv₀ hgrade₀
  obtain ⟨K, htail⟩ := eventually_atTop.1 hboundEventually
  let Mprefix : ℝ := Finset.sum (Finset.range K) fun k ↦ ‖(P k).coeffPair‖
  have hMprefix : 0 ≤ Mprefix := by
    exact Finset.sum_nonneg fun k _ ↦ norm_nonneg (P k).coeffPair
  refine ⟨Mtail + Mprefix, add_nonneg hMtail hMprefix, ?_⟩
  intro k
  by_cases hkTail : K ≤ k
  · exact (htail k hkTail).trans (le_add_of_nonneg_right hMprefix)
  · have hkMem : k ∈ Finset.range K := Finset.mem_range.mpr (lt_of_not_ge hkTail)
    have hkPrefix : ‖(P k).coeffPair‖ ≤ Mprefix :=
      Finset.single_le_sum (fun j _ ↦ norm_nonneg (P j).coeffPair) hkMem
    exact hkPrefix.trans (le_add_of_nonneg_left hMtail)

/-- Full polynomial-limit package.  Besides the global even and odd factor
limits, the consecutive products converge in the explicit max norm on their
four free coefficients and satisfy the manuscript-style height-tail bound. -/
theorem arnoldiOrbit2_polynomial_limits
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀) :
    ∃ tau : ℝ, ∃ pEven pOdd : MonicQuadratic, ∃ K : ℕ, ∃ C : ℝ,
      0 < tau ∧
      Tendsto (arnoldiNormalizerOrbit2 A v₀) atTop (nhds tau) ∧
      0 ≤ C ∧
      Tendsto (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
        atTop (nhds pEven.coeffPair) ∧
      Tendsto (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
        atTop (nhds pOdd.coeffPair) ∧
      Tendsto (fun k ↦ quadraticProductCoeff
          (arnoldiFactorOrbit2 A v₀ k)
          (arnoldiFactorOrbit2 A v₀ (k + 1))) atTop
        (nhds (quadraticProductCoeff pEven pOdd)) ∧
      ∀ n, dist
          (quadraticProductCoeff
            (arnoldiFactorOrbit2 A v₀ (n + K))
            (arnoldiFactorOrbit2 A v₀ (n + K + 1)))
          (quadraticProductCoeff pEven pOdd) ≤
        C * (tau ^ 2 - arnoldiHeightOrbit2 A v₀ (n + K)) := by
  let P := arnoldiFactorOrbit2 A v₀
  let H := arnoldiHeightOrbit2 A v₀
  let Q : ℕ → (ℝ × ℝ) × (ℝ × ℝ) :=
    fun k ↦ quadraticProductCoeff (P k) (P (k + 1))
  obtain ⟨pEven, pOdd, hpEven, hpOdd⟩ :=
    exists_arnoldiOrbit2_factor_limits A hA v₀ hv₀ hgrade₀
  obtain ⟨tau, htau, hσ⟩ :=
    arnoldiNormalizerOrbit2_tendsto A hA v₀ hv₀ hgrade₀
  have hH : Tendsto H atTop (nhds (tau ^ 2)) := by
    have hsquare := hσ.pow 2
    change Tendsto (fun k ↦ arnoldiNormalizerOrbit2 A v₀ k ^ 2)
      atTop (nhds (tau ^ 2))
    exact hsquare
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  have hinc : ∀ k, 0 ≤ heightIncrement H k := by
    intro k
    have hm := hsteps.height_le_succ hA k
    simpa only [heightIncrement, H, arnoldiHeightOrbit2] using sub_nonneg.mpr hm
  have hsum : Summable (heightIncrement H) := by
    change Summable (fun k ↦
      quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) (k + 1) -
        quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀) k)
    exact summable_arnoldiOrbit2_height_increment_of_initial_grade_three
      A hA v₀ hv₀ hgrade₀
  obtain ⟨Kvar, Cvar, hCvar, hvariation⟩ :=
    exists_arnoldiOrbit2_factor_variation_tail A hA v₀ hv₀ hgrade₀
  obtain ⟨M, hM, hboundEventually⟩ :=
    exists_eventually_arnoldiFactorOrbit2_coeffPair_bound
      A hA v₀ hv₀ hgrade₀
  obtain ⟨Kbound, hbound⟩ := eventually_atTop.1 hboundEventually
  let K := max Kvar Kbound
  let Cprod := (1 + 2 * M) * Cvar
  have hCprod : 0 ≤ Cprod := by
    dsimp only [Cprod]
    exact mul_nonneg (by linarith) hCvar.le
  have hQstep : ∀ n, dist (Q (n + K)) (Q ((n + 1) + K)) ≤
      Cprod * heightIncrement H (n + K) := by
    intro n
    have hkVar : Kvar ≤ n + K :=
      (le_max_left Kvar Kbound).trans (Nat.le_add_left K n)
    have hkBound : Kbound ≤ n + K + 1 :=
      (le_max_right Kvar Kbound).trans
        ((Nat.le_add_left K n).trans (Nat.le_add_right (n + K) 1))
    have hv := quadraticProductCoeff_succ_dist_le P H hCvar.le hM
      (hvariation (n + K) hkVar) (hbound (n + K + 1) hkBound)
    have hidx₁ : n + K + 1 = (n + 1) + K := by omega
    have hidx₂ : n + K + 2 = ((n + 1) + K) + 1 := by omega
    simpa only [Q, Cprod, hidx₁, hidx₂] using hv
  have hsumShift : Summable (heightIncrement (fun n ↦ H (n + K))) :=
    summable_heightIncrement_shift hsum K
  have hdsum : Summable (fun n ↦ Cprod * heightIncrement H (n + K)) :=
    hsumShift.mul_left Cprod |>.congr fun n ↦ by
      simp only [heightIncrement, Nat.add_assoc, Nat.add_comm K 1]
  have hQcauchy : CauchySeq (fun n ↦ Q (n + K)) :=
    cauchySeq_of_dist_le_of_summable
      (fun n ↦ Cprod * heightIncrement H (n + K)) hQstep hdsum
  obtain ⟨qLim, hqShift⟩ := cauchySeq_tendsto_of_complete hQcauchy
  have hqGlobal : Tendsto Q atTop (nhds qLim) :=
    (tendsto_add_atTop_iff_nat (f := Q) K).mp hqShift
  have hqEven : Tendsto (fun n ↦ Q (2 * n)) atTop
      (nhds (quadraticProductCoeff pEven pOdd)) := by
    apply tendsto_quadraticProductCoeff hpEven hpOdd
  have hqLimEven : Tendsto (fun n ↦ Q (2 * n)) atTop (nhds qLim) :=
    hqGlobal.comp tendsto_two_mul
  have hqEq : qLim = quadraticProductCoeff pEven pOdd :=
    tendsto_nhds_unique hqLimEven hqEven
  subst qLim
  refine ⟨tau, pEven, pOdd, K, Cprod, htau, hσ, hCprod,
    hpEven, hpOdd, ?_, ?_⟩
  · simpa only [Q, P] using hqGlobal
  · intro n
    let d : ℕ → ℝ := fun j ↦ Cprod * heightIncrement H (j + K)
    have hdist := dist_le_tsum_of_dist_le_of_tendsto d hQstep hdsum hqShift n
    have htailHasSum : HasSum (fun j ↦ d (n + j))
        (Cprod * (tau ^ 2 - H (n + K))) := by
      have ht := (hasSum_heightIncrement_tail H (tau ^ 2) hinc hH (n + K)).mul_left Cprod
      have heq : (fun j ↦ d (n + j)) =
          (fun j ↦ Cprod * heightIncrement H ((n + K) + j)) := by
        funext j
        dsimp only [d]
        rw [show n + j + K = n + K + j by omega]
      rw [heq]
      exact ht
    have htail := hdist.trans_eq htailHasSum.tsum_eq
    simpa only [Q, P, H, d, Nat.add_assoc] using htail

end Arnoldi

end
end Forsythe
