import Forsythe.FourNode.Continuity
import Forsythe.Spectral.PrincipalPerturbation

/-!
# Perturbation of the normalized principal-weight update

The selected squared components evolve exactly with the ambient Arnoldi
factor.  This module compares that rational update with the exact four-node
map driven by the intrinsic factor of the normalized principal weights.
All denominator and evaluation bounds are explicit hypotheses, as required
for the compact-tail application.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Evaluation of monic quadratics is Lipschitz in the concrete product norm
of their two free coefficients. -/
theorem abs_monicQuadratic_eval_sub_le
    (p q : MonicQuadratic) (t : ℝ) :
    |p.toPolynomial.eval t - q.toPolynomial.eval t| ≤
      (|t| + 1) * p.coeffDist q := by
  rw [MonicQuadratic.eval, MonicQuadratic.eval]
  let da := p.linearCoeff - q.linearCoeff
  let db := p.constantCoeff - q.constantCoeff
  let d := p.coeffDist q
  have hda : |da| ≤ d := by
    dsimp only [da, d, MonicQuadratic.coeffDist,
      MonicQuadratic.coeffPair, Prod.norm_def]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_left _ _
  have hdb : |db| ≤ d := by
    dsimp only [db, d, MonicQuadratic.coeffDist,
      MonicQuadratic.coeffPair, Prod.norm_def]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_right _ _
  have hd : 0 ≤ d := MonicQuadratic.coeffDist_nonneg _ _
  rw [show t ^ 2 + p.linearCoeff * t + p.constantCoeff -
      (t ^ 2 + q.linearCoeff * t + q.constantCoeff) = da * t + db by
    dsimp only [da, db]
    ring]
  calc
    |da * t + db| ≤ |da| * |t| + |db| := by
      simpa only [abs_mul] using abs_add_le (da * t) db
    _ ≤ d * |t| + d := add_le_add
      (mul_le_mul_of_nonneg_right hda (abs_nonneg t)) hdb
    _ = (|t| + 1) * d := by ring

/-- A fixed node-radius bound works simultaneously at all four nodes. -/
theorem abs_monicQuadratic_eval_sub_le_nodeRadius
    (lambda : Fin 4 → ℝ) (p q : MonicQuadratic) (i : Fin 4) :
    |p.toPolynomial.eval (lambda i) -
        q.toPolynomial.eval (lambda i)| ≤
      (FourNode.nodeRadius lambda + 1) * p.coeffDist q := by
  exact (abs_monicQuadratic_eval_sub_le p q (lambda i)).trans
    (mul_le_mul_of_nonneg_right
      (by linarith [FourNode.abs_node_le_nodeRadius lambda i])
      (MonicQuadratic.coeffDist_nonneg p q))

/-- Explicit Lipschitz constant for a normalized finite-node update driven
by two nearby monic quadratics. -/
def principalUpdatePolynomialLipschitzConstant
    (lambda : Fin 4 → ℝ) (M eta : ℝ) : ℝ :=
  let D := 2 * M * (FourNode.nodeRadius lambda + 1)
  D / eta + M ^ 2 * D / eta ^ 2

theorem principalUpdatePolynomialLipschitzConstant_nonneg
    (lambda : Fin 4 → ℝ) {M eta : ℝ}
    (hM : 0 ≤ M) (heta : 0 < eta) :
    0 ≤ principalUpdatePolynomialLipschitzConstant lambda M eta := by
  dsimp only [principalUpdatePolynomialLipschitzConstant]
  have hR : 0 ≤ FourNode.nodeRadius lambda + 1 :=
    add_nonneg (FourNode.nodeRadius_nonneg lambda) (by norm_num)
  have hD : 0 ≤ 2 * M * (FourNode.nodeRadius lambda + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hM) hR
  exact add_nonneg (div_nonneg hD heta.le)
    (div_nonneg (mul_nonneg (sq_nonneg M) hD) (sq_nonneg eta))

private theorem abs_div_sub_div_le
    {nx ny dx dy D N d eta : ℝ}
    (heta : 0 < eta) (hdx : eta ≤ dx) (hdy : eta ≤ dy)
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hd : 0 ≤ d)
    (hnum : |nx - ny| ≤ D * d) (hny : |ny| ≤ N)
    (hden : |dx - dy| ≤ D * d) :
    |nx / dx - ny / dy| ≤
      (D / eta + N * D / eta ^ 2) * d := by
  have hdxPos : 0 < dx := heta.trans_le hdx
  have hdyPos : 0 < dy := heta.trans_le hdy
  have hdenProd : eta ^ 2 ≤ dx * dy := by
    rw [pow_two]
    exact mul_le_mul hdx hdy heta.le hdxPos.le
  have hfirst : |(nx - ny) / dx| ≤ (D / eta) * d := by
    rw [abs_div, abs_of_pos hdxPos]
    calc
      |nx - ny| / dx ≤ (D * d) / dx :=
        div_le_div_of_nonneg_right hnum hdxPos.le
      _ ≤ (D * d) / eta := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ hdxPos heta).2 hdx) (mul_nonneg hD hd)
      _ = (D / eta) * d := by ring
  have hsecond : |ny * (dy - dx) / (dx * dy)| ≤
      (N * D / eta ^ 2) * d := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hdxPos hdyPos)]
    calc
      |ny| * |dy - dx| / (dx * dy) ≤
          (N * (D * d)) / (dx * dy) := by
        apply div_le_div_of_nonneg_right _ (mul_pos hdxPos hdyPos).le
        exact mul_le_mul hny (by simpa only [abs_sub_comm] using hden)
          (abs_nonneg _) hN
      _ ≤ (N * (D * d)) / eta ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ (mul_pos hdxPos hdyPos) (sq_pos_of_pos heta)).2
            hdenProd)
          (mul_nonneg hN (mul_nonneg hD hd))
      _ = (N * D / eta ^ 2) * d := by ring
  have hid : nx / dx - ny / dy =
      (nx - ny) / dx + ny * (dy - dx) / (dx * dy) := by
    field_simp [ne_of_gt hdxPos, ne_of_gt hdyPos]
    ring
  rw [hid]
  calc
    |(nx - ny) / dx + ny * (dy - dx) / (dx * dy)| ≤
        |(nx - ny) / dx| + |ny * (dy - dx) / (dx * dy)| := abs_add_le _ _
    _ ≤ (D / eta) * d + (N * D / eta ^ 2) * d :=
      add_le_add hfirst hsecond
    _ = (D / eta + N * D / eta ^ 2) * d := by ring

/-- The actual normalized principal-weight update differs from the exact
four-node map by at most an explicit constant times the coefficient distance
between the ambient and intrinsic monic factors. -/
theorem principalWeights_succ_sub_T_norm_le
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (k : ℕ)
    (hcomponent : ∀ i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    (hcomponentNext : ∀ i,
      component A hA (arnoldiOrbit2 A v₀ (k + 1)) (nodes i) ≠ 0)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 < eta)
    (hambientEval : ∀ i,
      |(arnoldiFactorOrbit2 A v₀ k).toPolynomial.eval
        ((nodes i : A.Eigenvalues) : ℝ)| ≤ M)
    (hintrinsicEval : ∀ i,
      |(FourNode.P (fun j ↦ ((nodes j : A.Eigenvalues) : ℝ))
        (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k) hcomponent)).toPolynomial.eval
          ((nodes i : A.Eigenvalues) : ℝ)| ≤ M)
    (hambientFloor : eta ≤ normalizedPrincipalResidual A hA nodes
      (arnoldiOrbit2 A v₀ k)
      (arnoldiFactorOrbit2 A v₀ k).toPolynomial)
    (hintrinsicFloor : eta ≤ FourNode.H
      (fun j ↦ ((nodes j : A.Eigenvalues) : ℝ))
      (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k) hcomponent)) :
    ‖FourNode.weightVector
        (principalWeights A hA nodes
          (arnoldiOrbit2 A v₀ (k + 1)) hcomponentNext) -
      FourNode.weightVector
        (FourNode.T (fun j ↦ ((nodes j : A.Eigenvalues) : ℝ))
          (fun _ _ hij ↦ hnodes (Subtype.ext hij))
          (principalWeights A hA nodes
            (arnoldiOrbit2 A v₀ k) hcomponent))‖ ≤
      principalUpdatePolynomialLipschitzConstant
          (fun j ↦ ((nodes j : A.Eigenvalues) : ℝ)) M eta *
        (arnoldiFactorOrbit2 A v₀ k).coeffDist
          (FourNode.P (fun j ↦ ((nodes j : A.Eigenvalues) : ℝ))
            (principalWeights A hA nodes
              (arnoldiOrbit2 A v₀ k) hcomponent)) := by
  let lambda : Fin 4 → ℝ :=
    fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let x := principalWeights A hA nodes
    (arnoldiOrbit2 A v₀ k) hcomponent
  let xnext := principalWeights A hA nodes
    (arnoldiOrbit2 A v₀ (k + 1)) hcomponentNext
  let pa := arnoldiFactorOrbit2 A v₀ k
  let pi := FourNode.P lambda x
  let d := pa.coeffDist pi
  let D := 2 * M * (FourNode.nodeRadius lambda + 1)
  let Ra := normalizedPrincipalResidual A hA nodes
    (arnoldiOrbit2 A v₀ k) pa.toPolynomial
  have hlambda : Function.Injective lambda := fun _ _ hij ↦
    hnodes (Subtype.ext hij)
  have hd : 0 ≤ d := MonicQuadratic.coeffDist_nonneg _ _
  have hR : 0 ≤ FourNode.nodeRadius lambda + 1 :=
    add_nonneg (FourNode.nodeRadius_nonneg lambda) (by norm_num)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (by norm_num) hM) hR
  have hsq (i : Fin 4) :
      |pa.toPolynomial.eval (lambda i) ^ 2 -
          pi.toPolynomial.eval (lambda i) ^ 2| ≤ D * d := by
    rw [show pa.toPolynomial.eval (lambda i) ^ 2 -
        pi.toPolynomial.eval (lambda i) ^ 2 =
      (pa.toPolynomial.eval (lambda i) - pi.toPolynomial.eval (lambda i)) *
        (pa.toPolynomial.eval (lambda i) + pi.toPolynomial.eval (lambda i)) by ring,
      abs_mul]
    calc
      |pa.toPolynomial.eval (lambda i) - pi.toPolynomial.eval (lambda i)| *
          |pa.toPolynomial.eval (lambda i) + pi.toPolynomial.eval (lambda i)| ≤
        ((FourNode.nodeRadius lambda + 1) * d) * (2 * M) := by
          apply mul_le_mul
          · exact abs_monicQuadratic_eval_sub_le_nodeRadius lambda pa pi i
          · exact (abs_add_le _ _).trans (by
              dsimp only [pa, pi, lambda, x]
              linarith [hambientEval i, hintrinsicEval i])
          · exact abs_nonneg _
          · exact mul_nonneg hR hd
      _ = D * d := by dsimp only [D]; ring
  have hRa : Ra =
      ∑ i, x i * pa.toPolynomial.eval (lambda i) ^ 2 := rfl
  have hHi : FourNode.H lambda x =
      ∑ i, x i * pi.toPolynomial.eval (lambda i) ^ 2 := by
    rw [FourNode.H, FourNode.height, FourNode.weightedPolyInner]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_two]
    ring
  have hden : |Ra - FourNode.H lambda x| ≤ D * d := by
    rw [hRa, hHi]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i, (x i * pa.toPolynomial.eval (lambda i) ^ 2 -
        x i * pi.toPolynomial.eval (lambda i) ^ 2)| ≤
          ∑ i, |x i *
              (pa.toPolynomial.eval (lambda i) ^ 2 -
                pi.toPolynomial.eval (lambda i) ^ 2)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        ring
      _ ≤ ∑ i, x i * (D * d) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (x.nonneg i)]
        exact mul_le_mul_of_nonneg_left (hsq i) (x.nonneg i)
      _ = D * d := by
        rw [← Finset.sum_mul, x.sum_eq_one, one_mul]
  have hcomponentBound (i : Fin 4) :
      |xnext i - FourNode.T lambda hlambda x i| ≤
        principalUpdatePolynomialLipschitzConstant lambda M eta * d := by
    dsimp only [xnext]
    rw [principalWeights_apply,
      normalizedPrincipalWeight_arnoldiOrbit2_succ
        A hA v₀ hv₀ hgrade₀ nodes k hcomponent hcomponentNext i,
      FourNode.T_weight]
    change |(x i * pa.toPolynomial.eval (lambda i) ^ 2) / Ra -
      (x i * pi.toPolynomial.eval (lambda i) ^ 2) /
        FourNode.H lambda x| ≤ _
    have hnum : |x i * pa.toPolynomial.eval (lambda i) ^ 2 -
        x i * pi.toPolynomial.eval (lambda i) ^ 2| ≤ D * d := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (x.nonneg i)]
      exact (mul_le_mul_of_nonneg_left (hsq i) (x.nonneg i)).trans
        (by
          have hxone := FourNode.weight_le_one x i
          nlinarith [mul_nonneg hD hd])
    have hny : |x i * pi.toPolynomial.eval (lambda i) ^ 2| ≤ M ^ 2 := by
      rw [abs_mul, abs_of_nonneg (x.nonneg i), abs_pow]
      have he := hintrinsicEval i
      have hsquare := (sq_le_sq₀ (abs_nonneg _) hM).2 he
      calc
        x i * |pi.toPolynomial.eval (lambda i)| ^ 2 ≤
            1 * M ^ 2 := mul_le_mul (FourNode.weight_le_one x i)
              hsquare (sq_nonneg _) (by norm_num)
        _ = M ^ 2 := one_mul _
    simpa only [principalUpdatePolynomialLipschitzConstant, D, Ra, d] using
      abs_div_sub_div_le heta hambientFloor hintrinsicFloor hD
        (sq_nonneg M) hd hnum hny hden
  have hconst : 0 ≤
      principalUpdatePolynomialLipschitzConstant lambda M eta :=
    principalUpdatePolynomialLipschitzConstant_nonneg lambda hM heta
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hconst hd)]
  intro i
  change |xnext i - FourNode.T lambda hlambda x i| ≤
    principalUpdatePolynomialLipschitzConstant lambda M eta * d
  exact hcomponentBound i

end

end Spectral
end Forsythe
