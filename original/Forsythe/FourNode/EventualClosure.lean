import Forsythe.FourNode.Closure

/-!
# Eventual-tail form of four-node scalar closure

The spectral argument naturally supplies denominator floors, update defects,
and sign conditions only on an orbit tail.  This module shifts that tail once,
applies the all-indices closure theorem, and shifts the resulting limit back.
No asymptotic condition is weakened or hidden: every eventual hypothesis below
is exactly the corresponding field used by `PerturbationFloors` or by the
scalar recurrence.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Set Topology

noncomputable section

/-- Tail-facing version of `exists_tendsto_rhoSeq_of_geometric_weightDefect`.

The geometric constant changes from `B` to `B * theta ^ K` after shifting by
`K`; the rate itself is unchanged. -/
theorem exists_tendsto_rhoSeq_of_eventually_geometric_weightDefect
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights)
    {delta eta B theta Cc : ℝ}
    (hdelta : 0 < delta) (heta : 0 < eta) (hB : 0 ≤ B)
    (hthetaPos : 0 < theta) (hthetaLt : theta < 1)
    (hfloors : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k) ∧
      delta ≤ weightedMomentGramDet lambda
        (exactUpdateSeq lambda hlambda x k) ∧
      delta ≤ weightedMomentGramDet lambda
        (T lambda hlambda (exactUpdateSeq lambda hlambda x k)) ∧
      eta ≤ H lambda (x k) ∧
      eta ≤ H lambda (exactUpdateSeq lambda hlambda x k))
    (hdefect : ∀ᶠ k in atTop,
      ‖weightVector (x (k + 1)) -
          weightVector (exactUpdateSeq lambda hlambda x k)‖ ≤
        B * theta ^ k)
    (hden : ∀ᶠ k in atTop,
      newRemainderCoeff lambda hlambda x k ≠ 0)
    (hmpos : ∀ᶠ k in atTop,
      0 < remainderMultiplier lambda hlambda x k)
    (hm : Tendsto (remainderMultiplier lambda hlambda x)
      atTop (nhds 1))
    (hAlphaZero : Tendsto (alphaSeq lambda hlambda x)
      atTop (nhds 0))
    (left right : Fin 4) (hgap : lambda left < lambda right)
    (hCc : 0 ≤ Cc)
    (hcBound : ∀ᶠ k in atTop,
      |rhoIncrementCoeff lambda hlambda x k| ≤ Cc)
    (hRho : ∀ᶠ k in atTop,
      rhoSeq lambda x k ∈ Set.Icc (lambda left) (lambda right))
    (hlocal : ScalarDynamics.EventuallyLocallySeparatedCoefficient
      (rhoSeq lambda x) (rhoIncrementCoeff lambda hlambda x)
      (lambda left) (lambda right)) :
    ∃ rhoLim ∈ Set.Icc (lambda left) (lambda right),
      Tendsto (rhoSeq lambda x) atTop (nhds rhoLim) := by
  have hall := hfloors.and <|
    hdefect.and <| hden.and <| hmpos.and <| hcBound.and hRho
  obtain ⟨K, hK⟩ := eventually_atTop.1 hall
  let xs : ℕ → Weights := fun k ↦ x (k + K)
  let Bs : ℝ := B * theta ^ K
  have hBs : 0 ≤ Bs := by
    exact mul_nonneg hB (pow_nonneg hthetaPos.le K)
  have hfloorsShift : PerturbationFloors lambda hlambda xs delta eta := by
    refine
      { gram_x := ?_
        gram_y := ?_
        gram_T_y := ?_
        height_x := ?_
        height_y := ?_ }
    · intro k
      have hk := (hK (k + K) (by omega)).1
      simpa only [xs] using hk.1
    · intro k
      have hk := (hK (k + K) (by omega)).1
      simpa only [xs, exactUpdateSeq] using hk.2.1
    · intro k
      have hk := (hK (k + K) (by omega)).1
      simpa only [xs, exactUpdateSeq] using hk.2.2.1
    · intro k
      have hk := (hK (k + K) (by omega)).1
      simpa only [xs] using hk.2.2.2.1
    · intro k
      have hk := (hK (k + K) (by omega)).1
      simpa only [xs, exactUpdateSeq] using hk.2.2.2.2
  have hdefectShift :
      HasGeometricWeightDefect lambda hlambda xs Bs theta := by
    intro k
    have hk := (hK (k + K) (by omega)).2.1
    have hk' :
        ‖weightVector (xs (k + 1)) -
            weightVector (exactUpdateSeq lambda hlambda xs k)‖ ≤
          B * theta ^ (k + K) := by
      simpa only [xs, exactUpdateSeq, Nat.add_assoc,
        Nat.add_comm K 1, Nat.add_left_comm K 1] using hk
    calc
      ‖weightVector (xs (k + 1)) -
          weightVector (exactUpdateSeq lambda hlambda xs k)‖ ≤
          B * theta ^ (k + K) := hk'
      _ = Bs * theta ^ k := by
        simp only [Bs, pow_add]
        ring
  have hdenShift : ∀ k,
      newRemainderCoeff lambda hlambda xs k ≠ 0 := by
    intro k
    have hk := (hK (k + K) (by omega)).2.2.1
    simpa only [xs, newRemainderCoeff, exactUpdateSeq, rhoSeq] using hk
  have hmposShift : ∀ k,
      0 < remainderMultiplier lambda hlambda xs k := by
    intro k
    have hk := (hK (k + K) (by omega)).2.2.2.1
    simpa only [xs, remainderMultiplier, oldRemainderCoeff,
      newRemainderCoeff, exactUpdateSeq, rhoSeq] using hk
  have hmShift : Tendsto (remainderMultiplier lambda hlambda xs)
      atTop (nhds 1) := by
    have ht := hm.comp (tendsto_add_atTop_nat K)
    change Tendsto
      (fun k ↦ remainderMultiplier lambda hlambda x (k + K))
      atTop (nhds 1)
    simpa only [Function.comp_def] using ht
  have hAlphaShift : Tendsto (alphaSeq lambda hlambda xs)
      atTop (nhds 0) := by
    have ht := hAlphaZero.comp (tendsto_add_atTop_nat K)
    change Tendsto (fun k ↦ alphaSeq lambda hlambda x (k + K))
      atTop (nhds 0)
    simpa only [Function.comp_def] using ht
  have hcBoundShift : ∀ k,
      |rhoIncrementCoeff lambda hlambda xs k| ≤ Cc := by
    intro k
    have hk := (hK (k + K) (by omega)).2.2.2.2.1
    simpa only [xs, rhoIncrementCoeff, exactUpdateSeq, rhoSeq] using hk
  have hRhoShift : ∀ k,
      rhoSeq lambda xs k ∈ Set.Icc (lambda left) (lambda right) := by
    intro k
    have hk := (hK (k + K) (by omega)).2.2.2.2.2
    simpa only [xs, rhoSeq] using hk
  have hlocalShift : ScalarDynamics.EventuallyLocallySeparatedCoefficient
      (rhoSeq lambda xs) (rhoIncrementCoeff lambda hlambda xs)
      (lambda left) (lambda right) := by
    intro lo hi hlo hlt hhi
    obtain ⟨e, he, hpos | hneg⟩ := hlocal lo hi hlo hlt hhi
    · refine ⟨e, he, Or.inl ?_⟩
      have hs := (tendsto_add_atTop_nat K).eventually hpos
      simpa only [xs, rhoSeq, rhoIncrementCoeff, exactUpdateSeq] using hs
    · refine ⟨e, he, Or.inr ?_⟩
      have hs := (tendsto_add_atTop_nat K).eventually hneg
      simpa only [xs, rhoSeq, rhoIncrementCoeff, exactUpdateSeq] using hs
  obtain ⟨rhoLim, hrhoLim, htendsto⟩ :=
    exists_tendsto_rhoSeq_of_geometric_weightDefect
      hlambda xs hdelta heta hBs hthetaPos hthetaLt
      hfloorsShift hdefectShift hdenShift hmposShift hmShift hAlphaShift
      left right hgap hCc hcBoundShift hRhoShift hlocalShift
  refine ⟨rhoLim, hrhoLim, ?_⟩
  apply (tendsto_add_atTop_iff_nat K).mp
  change Tendsto (fun n ↦ rhoSeq lambda x (n + K))
    atTop (nhds rhoLim) at htendsto
  exact htendsto

end

end FourNode
end Forsythe
