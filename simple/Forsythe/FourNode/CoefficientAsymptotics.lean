import Forsythe.Dynamics.ScalarClosure
import Forsythe.FourNode.Gap
import Forsythe.FourNode.Perturbation

/-!
# Bounds for the four-node barycentric increment coefficient

On the ordered middle gap the nodal quartic is nonnegative, and is strictly
positive on every compact interior subinterval.  A positive limiting height
therefore gives both the global tail bound and the local one-sided separation
required by the scalar closure lemma.
-/

set_option autoImplicit false

namespace Forsythe
namespace FourNode

open Filter Polynomial Set Topology

noncomputable section

/-- Middle-gap confinement and convergence of the exact-update height give a
uniform tail bound for the coefficient in the `rho` increment, as well as
positive local separation on every compact interior subinterval. -/
theorem exists_rhoIncrementCoeff_bound_and_local_separation
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    (x : ℕ → Weights) {tau : ℝ} (htau : 0 < tau)
    (hRho : ∀ᶠ k in atTop,
      rhoSeq lambda x k ∈ Icc (lambda 1) (lambda 2))
    (hHeight : Tendsto (fun k ↦
      H lambda (exactUpdateSeq lambda hlambda.injective x k))
      atTop (nhds (tau ^ 2))) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      (∀ᶠ k in atTop,
        |rhoIncrementCoeff lambda hlambda.injective x k| ≤ Cc) ∧
      ScalarDynamics.EventuallyLocallySeparatedCoefficient
        (rhoSeq lambda x)
        (rhoIncrementCoeff lambda hlambda.injective x)
        (lambda 1) (lambda 2) := by
  let J : Set ℝ := Icc (lambda 1) (lambda 2)
  have hJnonempty : J.Nonempty :=
    nonempty_Icc.2 (hlambda (by decide)).le
  obtain ⟨tMax, htMax, hMax⟩ := isCompact_Icc.exists_isMaxOn hJnonempty
    (nodalQuartic lambda).continuous.abs.continuousOn
  let PiMax : ℝ := |(nodalQuartic lambda).eval tMax|
  have hPiMax : 0 ≤ PiMax := abs_nonneg _
  let heightFloor : ℝ := tau ^ 2 / 2
  have hheightFloor : 0 < heightFloor := by
    dsimp only [heightFloor]
    positivity
  have hHeightLower : ∀ᶠ k in atTop,
      heightFloor < H lambda
        (exactUpdateSeq lambda hlambda.injective x k) := by
    apply (tendsto_order.1 hHeight).1
    dsimp only [heightFloor]
    nlinarith [sq_pos_of_pos htau]
  let Cc : ℝ := PiMax / heightFloor
  have hCc : 0 ≤ Cc := div_nonneg hPiMax hheightFloor.le
  have hcBound : ∀ᶠ k in atTop,
      |rhoIncrementCoeff lambda hlambda.injective x k| ≤ Cc := by
    filter_upwards [hRho, hHeightLower] with k hrho hheight
    have hPiNonneg := nodalQuartic_eval_nonneg_on_middleGap hlambda hrho
    have hPiLeAbs :
        |(nodalQuartic lambda).eval (rhoSeq lambda x k)| ≤ PiMax :=
      hMax hrho
    have hPiLe :
        (nodalQuartic lambda).eval (rhoSeq lambda x k) ≤ PiMax := by
      simpa only [abs_of_nonneg hPiNonneg] using hPiLeAbs
    have hheightPos : 0 <
        H lambda (exactUpdateSeq lambda hlambda.injective x k) :=
      hheightFloor.trans hheight
    rw [rhoIncrementCoeff, abs_div, abs_of_pos hheightPos,
      abs_of_nonneg hPiNonneg]
    calc
      (nodalQuartic lambda).eval (rhoSeq lambda x k) /
          H lambda (exactUpdateSeq lambda hlambda.injective x k) ≤
        PiMax / H lambda (exactUpdateSeq lambda hlambda.injective x k) :=
          div_le_div_of_nonneg_right hPiLe hheightPos.le
      _ ≤ PiMax / heightFloor :=
        div_le_div_of_nonneg_left hPiMax hheightFloor hheight.le
      _ = Cc := rfl
  refine ⟨Cc, hCc, hcBound, ?_⟩
  intro lo hi hlo hlohi hhi
  let K : Set ℝ := Icc lo hi
  have hKnonempty : K.Nonempty := nonempty_Icc.2 hlohi.le
  have hPiPos : ∀ t ∈ K, 0 < (nodalQuartic lambda).eval t := by
    intro t ht
    apply nodalQuartic_eval_pos_on_middleGap hlambda
    exact ⟨hlo.trans_le ht.1, ht.2.trans_lt hhi⟩
  obtain ⟨piFloor, hpiFloor, hPiFloor⟩ :=
    isCompact_Icc.exists_forall_le'
      (nodalQuartic lambda).continuous.continuousOn hPiPos
  let heightCeil : ℝ := tau ^ 2 + 1
  have hheightCeil : 0 < heightCeil := by positivity
  have hHeightUpper : ∀ᶠ k in atTop,
      H lambda (exactUpdateSeq lambda hlambda.injective x k) < heightCeil := by
    apply (tendsto_order.1 hHeight).2
    dsimp only [heightCeil]
    linarith
  let eta : ℝ := piFloor / heightCeil
  have heta : 0 < eta := div_pos hpiFloor hheightCeil
  refine ⟨eta, heta, Or.inl ?_⟩
  filter_upwards [hHeightLower, hHeightUpper] with k hheightLow hheightHigh
  intro hrho
  have hPi := hPiFloor (rhoSeq lambda x k) hrho
  have hheightPos : 0 <
      H lambda (exactUpdateSeq lambda hlambda.injective x k) :=
    hheightFloor.trans hheightLow
  rw [rhoIncrementCoeff]
  calc
    eta = piFloor / heightCeil := rfl
    _ ≤ piFloor /
        H lambda (exactUpdateSeq lambda hlambda.injective x k) :=
      div_le_div_of_nonneg_left hpiFloor.le hheightPos hheightHigh.le
    _ ≤ (nodalQuartic lambda).eval (rhoSeq lambda x k) /
        H lambda (exactUpdateSeq lambda hlambda.injective x k) :=
      div_le_div_of_nonneg_right hPi hheightPos.le

/-- If `alpha` tends to zero, the exact-update barycentric parameter differs
from the old parameter by a quantity tending to zero. -/
theorem tendsto_rhoSeq_sub_rho_exactUpdate_of_alpha_zero
    {lambda : Fin 4 → ℝ} (hlambda : StrictMono lambda)
    (x : ℕ → Weights) {Cc : ℝ} (_hCc : 0 ≤ Cc)
    (hcBound : ∀ᶠ k in atTop,
      |rhoIncrementCoeff lambda hlambda.injective x k| ≤ Cc)
    (hAlpha : Tendsto (alphaSeq lambda hlambda.injective x)
      atTop (nhds 0)) :
    Tendsto (fun k ↦
      rhoSeq lambda x k -
        rho lambda (exactUpdateSeq lambda hlambda.injective x k))
      atTop (nhds 0) := by
  have hAlphaAbs : Tendsto (fun k ↦
      |alphaSeq lambda hlambda.injective x k|) atTop (nhds 0) := by
    simpa only [abs_zero] using hAlpha.abs
  have hupper : Tendsto (fun k ↦ Cc *
      |alphaSeq lambda hlambda.injective x k|) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hAlphaAbs
  have hproductAbs : Tendsto (fun k ↦
      |rhoIncrementCoeff lambda hlambda.injective x k *
        alphaSeq lambda hlambda.injective x k|) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun k ↦ abs_nonneg _
    · filter_upwards [hcBound] with k hk
      calc
        |rhoIncrementCoeff lambda hlambda.injective x k *
            alphaSeq lambda hlambda.injective x k| =
          |rhoIncrementCoeff lambda hlambda.injective x k| *
            |alphaSeq lambda hlambda.injective x k| := abs_mul _ _
        _ ≤ Cc * |alphaSeq lambda hlambda.injective x k| :=
          mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    · exact hupper
  have hproduct : Tendsto (fun k ↦
      rhoIncrementCoeff lambda hlambda.injective x k *
        alphaSeq lambda hlambda.injective x k) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 hproductAbs
  have hnegative : Tendsto (fun k ↦
      -(rhoIncrementCoeff lambda hlambda.injective x k *
        alphaSeq lambda hlambda.injective x k)) atTop (nhds 0) := by
    simpa only [neg_zero] using hproduct.neg
  apply hnegative.congr'
  exact Eventually.of_forall fun k ↦ by
    change -(rhoIncrementCoeff lambda hlambda.injective x k *
        alphaSeq lambda hlambda.injective x k) =
      rhoSeq lambda x k -
        rho lambda (exactUpdateSeq lambda hlambda.injective x k)
    have h := rho_exactUpdate_sub_eq_coeff_mul_alpha
      hlambda.injective x k
    linarith

end

end FourNode
end Forsythe
