import Forsythe.FourNode.Perturbation

/-!
# Denominator floors for an asymptotically exact four-node orbit

If the states themselves have uniform Gram and height floors and their update
defect tends to zero, then the exact updates and exact two-step updates inherit
common tail floors.  This is the compact-denominator step needed by the
explicit `rho` and `alpha` perturbation estimates.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Topology

noncomputable section

/-- Uniform floors propagate from an asymptotically exact sequence to the
states appearing in `PerturbationFloors`. -/
theorem exists_eventually_perturbationFloors_of_updateDefect_tendsto_zero
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (x : ℕ → Weights) {delta₀ eta₀ : ℝ}
    (hdelta₀ : 0 < delta₀) (heta₀ : 0 < eta₀)
    (hgram : ∀ᶠ k in atTop,
      delta₀ ≤ weightedMomentGramDet lambda (x k))
    (hheight : ∀ᶠ k in atTop, eta₀ ≤ H lambda (x k))
    (hdefectZero : Tendsto
      (fun k ↦ ‖weightVector (x (k + 1)) -
        weightVector (exactUpdateSeq lambda hlambda x k)‖)
      atTop (nhds 0)) :
    ∃ delta eta : ℝ, 0 < delta ∧ 0 < eta ∧
      ∀ᶠ k in atTop,
        delta ≤ weightedMomentGramDet lambda (x k) ∧
        delta ≤ weightedMomentGramDet lambda
          (exactUpdateSeq lambda hlambda x k) ∧
        delta ≤ weightedMomentGramDet lambda
          (T lambda hlambda (exactUpdateSeq lambda hlambda x k)) ∧
        eta ≤ H lambda (x k) ∧
        eta ≤ H lambda (exactUpdateSeq lambda hlambda x k) := by
  let delta : ℝ := delta₀ / 2
  let eta : ℝ := eta₀ / 2
  let d : ℕ → ℝ := fun k ↦
    ‖weightVector (x (k + 1)) -
      weightVector (exactUpdateSeq lambda hlambda x k)‖
  let y : ℕ → Weights := fun k ↦ exactUpdateSeq lambda hlambda x k
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hdZero : Tendsto d atTop (nhds 0) := by
    simpa only [d] using hdefectZero
  have hgramShift : ∀ᶠ k in atTop,
      delta₀ ≤ weightedMomentGramDet lambda (x (k + 1)) :=
    (tendsto_add_atTop_nat 1).eventually hgram
  have hheightShift : ∀ᶠ k in atTop,
      eta₀ ≤ H lambda (x (k + 1)) :=
    (tendsto_add_atTop_nat 1).eventually hheight
  have hgramErrorZero : Tendsto
      (fun k ↦ gramLipschitzConstant lambda * d k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdZero
  have hgramSmall : ∀ᶠ k in atTop,
      gramLipschitzConstant lambda * d k < delta₀ / 2 :=
    (tendsto_order.1 hgramErrorZero).2 _ (by linarith)
  have hyGram : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (y k) := by
    filter_upwards [hgramShift, hgramSmall] with k hxGram hsmall
    have habs := abs_weightedMomentGramDet_sub_le lambda (x (k + 1)) (y k)
    have habs' :
        |weightedMomentGramDet lambda (x (k + 1)) -
          weightedMomentGramDet lambda (y k)| ≤
          gramLipschitzConstant lambda * d k := by
      simpa only [d, y] using habs
    have hupper := le_of_abs_le habs'
    dsimp only [delta]
    nlinarith
  have hxGramDelta : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x k) :=
    hgram.mono fun _ hk ↦ by dsimp only [delta]; linarith
  have hxGramDeltaShift : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (x (k + 1)) :=
    (tendsto_add_atTop_nat 1).eventually hxGramDelta
  have hheightErrorZero : Tendsto
      (fun k ↦ heightLipschitzConstant lambda delta * d k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdZero
  have hheightSmall : ∀ᶠ k in atTop,
      heightLipschitzConstant lambda delta * d k < eta₀ / 2 :=
    (tendsto_order.1 hheightErrorZero).2 _ (by linarith)
  have hyHeight : ∀ᶠ k in atTop, eta ≤ H lambda (y k) := by
    filter_upwards [hheightShift, hxGramDeltaShift, hyGram, hheightSmall]
      with k hxHeight hxGram hyGramK hsmall
    have habs := abs_height_sub_le_of_gram_floor lambda (x (k + 1)) (y k)
      hdelta hxGram hyGramK
    have habs' : |H lambda (x (k + 1)) - H lambda (y k)| ≤
        heightLipschitzConstant lambda delta * d k := by
      simpa only [d, y] using habs
    have hupper := le_of_abs_le habs'
    dsimp only [eta]
    nlinarith
  have hxHeightEta : ∀ᶠ k in atTop, eta ≤ H lambda (x k) :=
    hheight.mono fun _ hk ↦ by dsimp only [eta]; linarith
  have hxHeightEtaShift : ∀ᶠ k in atTop,
      eta ≤ H lambda (x (k + 1)) :=
    (tendsto_add_atTop_nat 1).eventually hxHeightEta
  let L : ℝ := nextWeightLipschitzConstant lambda delta eta
  have hL : 0 ≤ L := by
    exact nextWeightLipschitzConstant_nonneg lambda hdelta heta
  have hTyDistanceBound : ∀ᶠ k in atTop,
      ‖weightVector (T lambda hlambda (y k)) -
          weightVector (x (k + 2))‖ ≤ L * d k + d (k + 1) := by
    filter_upwards [hyGram, hxGramDeltaShift, hyHeight,
      hxHeightEtaShift] with k hyGramK hxGramK hyHeightK hxHeightK
    have hT := T_weightVector_sub_norm_le_of_floors hlambda
      (y k) (x (k + 1)) hdelta heta
      hyGramK hxGramK hyHeightK hxHeightK
    have hT' :
        ‖weightVector (T lambda hlambda (y k)) -
          weightVector (T lambda hlambda (x (k + 1)))‖ ≤ L * d k := by
      calc
        ‖weightVector (T lambda hlambda (y k)) -
          weightVector (T lambda hlambda (x (k + 1)))‖ ≤
            L * ‖weightVector (y k) - weightVector (x (k + 1))‖ := by
              simpa only [L] using hT
        _ = L * d k := by
          congr 1
          dsimp only [d, y]
          rw [norm_sub_rev]
    have hadd :
        weightVector (T lambda hlambda (y k)) - weightVector (x (k + 2)) =
          (weightVector (T lambda hlambda (y k)) -
            weightVector (T lambda hlambda (x (k + 1)))) +
          (weightVector (T lambda hlambda (x (k + 1))) -
            weightVector (x (k + 2))) := by
      abel
    calc
      ‖weightVector (T lambda hlambda (y k)) -
          weightVector (x (k + 2))‖ ≤
          ‖weightVector (T lambda hlambda (y k)) -
            weightVector (T lambda hlambda (x (k + 1)))‖ +
          ‖weightVector (T lambda hlambda (x (k + 1))) -
            weightVector (x (k + 2))‖ := by
        rw [hadd]
        exact norm_add_le _ _
      _ ≤ L * d k + d (k + 1) := by
        apply add_le_add
        · exact hT'
        · dsimp only [d, y, exactUpdateSeq]
          rw [norm_sub_rev]
  have hdShiftZero : Tendsto (fun k ↦ d (k + 1)) atTop (nhds 0) :=
    hdZero.comp (tendsto_add_atTop_nat 1)
  have hTyBoundZero : Tendsto (fun k ↦ L * d k + d (k + 1))
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_const_nhds.mul hdZero).add hdShiftZero
  have hTyDistanceZero : Tendsto
      (fun k ↦ ‖weightVector (T lambda hlambda (y k)) -
        weightVector (x (k + 2))‖) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun k ↦ norm_nonneg _
    · exact hTyDistanceBound
    · exact hTyBoundZero
  have hgramShiftTwo : ∀ᶠ k in atTop,
      delta₀ ≤ weightedMomentGramDet lambda (x (k + 2)) :=
    (tendsto_add_atTop_nat 2).eventually hgram
  have hTyGramErrorZero : Tendsto
      (fun k ↦ gramLipschitzConstant lambda *
        ‖weightVector (T lambda hlambda (y k)) -
          weightVector (x (k + 2))‖) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hTyDistanceZero
  have hTyGramSmall : ∀ᶠ k in atTop,
      gramLipschitzConstant lambda *
        ‖weightVector (T lambda hlambda (y k)) -
          weightVector (x (k + 2))‖ < delta₀ / 2 :=
    (tendsto_order.1 hTyGramErrorZero).2 _ (by linarith)
  have hTyGram : ∀ᶠ k in atTop,
      delta ≤ weightedMomentGramDet lambda (T lambda hlambda (y k)) := by
    filter_upwards [hgramShiftTwo, hTyGramSmall] with k hxGram hsmall
    have habs := abs_weightedMomentGramDet_sub_le lambda
      (T lambda hlambda (y k)) (x (k + 2))
    have habs' :
        |weightedMomentGramDet lambda (T lambda hlambda (y k)) -
          weightedMomentGramDet lambda (x (k + 2))| ≤
        gramLipschitzConstant lambda *
          ‖weightVector (T lambda hlambda (y k)) -
            weightVector (x (k + 2))‖ := habs
    have hlower := neg_le_of_abs_le habs'
    dsimp only [delta]
    nlinarith
  refine ⟨delta, eta, hdelta, heta, ?_⟩
  filter_upwards [hxGramDelta, hyGram, hTyGram, hxHeightEta, hyHeight]
    with k hxG hyG hTyG hxH hyH
  simpa only [y] using ⟨hxG, hyG, hTyG, hxH, hyH⟩

end

end FourNode
end Forsythe
