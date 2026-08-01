import Forsythe.Polynomial.MomentStability
import Forsythe.Spectral.ExteriorMass

/-!
# Explicit polynomial perturbation from exterior mass

The full Arnoldi factor and the factor of the normalized four principal
weights solve the same rational moment system with nearby moments.  Combining
the exterior-moment estimate with the concrete Cramer stability theorem gives
an explicit coefficient bound linear in exterior mass.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A common bound for the first three full and principal moments. -/
def spectralMomentBound (A : Module.End ℝ E) : ℝ :=
  1 + eigenvalueAbsSum A + eigenvalueAbsSum A ^ 2 + eigenvalueAbsSum A ^ 3

/-- Sum of the first three spectral power bounds. -/
def spectralMomentScale (A : Module.End ℝ E) : ℝ :=
  eigenvalueAbsSum A + eigenvalueAbsSum A ^ 2 + eigenvalueAbsSum A ^ 3

/-- Explicit rational Lipschitz constant for the two free coefficients. -/
def principalFactorPerturbationConstant
    (A : Module.End ℝ E) (kappa : ℝ) : ℝ :=
  let M := spectralMomentBound A
  (4 * M + 2) / kappa +
    (2 * M ^ 2 + M) * (2 * M + 1) / kappa ^ 2

theorem spectralMomentBound_nonneg (A : Module.End ℝ E) :
    0 ≤ spectralMomentBound A := by
  have hB := eigenvalueAbsSum_nonneg A
  dsimp only [spectralMomentBound]
  positivity

theorem spectralMomentScale_nonneg (A : Module.End ℝ E) :
    0 ≤ spectralMomentScale A := by
  have hB := eigenvalueAbsSum_nonneg A
  dsimp only [spectralMomentScale]
  positivity

omit [FiniteDimensional ℝ E] in
/-- The intrinsic Cramer formula reduces to the unit-mass moment formula on
a unit vector. -/
theorem arnoldiPoly2_eq_quadraticOfUnitMoments
    (A : Module.End ℝ E) (v : E) (hv : ‖v‖ = 1) :
    arnoldiPoly2 A v = MomentStability.quadraticOfUnitMoments
      (moment A v 1) (moment A v 2) (moment A v 3) := by
  have hm0 : moment A v 0 = 1 := by
    rw [moment_zero, real_inner_self_eq_norm_sq, hv, one_pow]
  apply MonicQuadratic.ext
  · change
      (moment A v 1 * moment A v 2 - moment A v 0 * moment A v 3) /
          momentGramDet A v =
        (moment A v 1 * moment A v 2 - moment A v 3) /
          MomentStability.unitMomentDet (moment A v 1) (moment A v 2)
    rw [momentGramDet, MomentStability.unitMomentDet, hm0]
    ring
  · change
      (moment A v 1 * moment A v 3 - moment A v 2 ^ 2) /
          momentGramDet A v =
        (moment A v 1 * moment A v 3 - moment A v 2 ^ 2) /
          MomentStability.unitMomentDet (moment A v 1) (moment A v 2)
    rw [momentGramDet, MomentStability.unitMomentDet, hm0]
    ring

/-- The four-node Cramer formula is the same unit-mass moment formula. -/
theorem FourNode.P_eq_quadraticOfUnitMoments
    (lambda : Fin 4 → ℝ) (x : FourNode.Weights) :
    FourNode.P lambda x = MomentStability.quadraticOfUnitMoments
      (FourNode.weightedMoment lambda x 1)
      (FourNode.weightedMoment lambda x 2)
      (FourNode.weightedMoment lambda x 3) := by
  have hm0 := FourNode.weightedMoment_zero lambda x
  apply MonicQuadratic.ext
  · change
      (FourNode.weightedMoment lambda x 1 *
          FourNode.weightedMoment lambda x 2 -
        FourNode.weightedMoment lambda x 0 *
          FourNode.weightedMoment lambda x 3) /
          FourNode.weightedMomentGramDet lambda x =
        (FourNode.weightedMoment lambda x 1 *
          FourNode.weightedMoment lambda x 2 -
          FourNode.weightedMoment lambda x 3) /
        MomentStability.unitMomentDet
          (FourNode.weightedMoment lambda x 1)
          (FourNode.weightedMoment lambda x 2)
    rw [FourNode.weightedMomentGramDet, MomentStability.unitMomentDet, hm0]
    ring
  · change
      (FourNode.weightedMoment lambda x 1 *
          FourNode.weightedMoment lambda x 3 -
        FourNode.weightedMoment lambda x 2 ^ 2) /
          FourNode.weightedMomentGramDet lambda x =
        (FourNode.weightedMoment lambda x 1 *
          FourNode.weightedMoment lambda x 3 -
          FourNode.weightedMoment lambda x 2 ^ 2) /
        MomentStability.unitMomentDet
          (FourNode.weightedMoment lambda x 1)
          (FourNode.weightedMoment lambda x 2)
    rw [FourNode.weightedMomentGramDet, MomentStability.unitMomentDet, hm0]
    ring

omit [FiniteDimensional ℝ E] in
/-- The unit-moment determinants are the intrinsic and four-node Gram
determinants. -/
theorem unitMomentDet_eq_momentGramDet
    (A : Module.End ℝ E) (v : E) (hv : ‖v‖ = 1) :
    MomentStability.unitMomentDet (moment A v 1) (moment A v 2) =
      momentGramDet A v := by
  have hm0 : moment A v 0 = 1 := by
    rw [moment_zero, real_inner_self_eq_norm_sq, hv, one_pow]
  rw [MomentStability.unitMomentDet, momentGramDet, hm0]
  ring

theorem FourNode.unitMomentDet_eq_weightedMomentGramDet
    (lambda : Fin 4 → ℝ) (x : FourNode.Weights) :
    MomentStability.unitMomentDet
        (FourNode.weightedMoment lambda x 1)
        (FourNode.weightedMoment lambda x 2) =
      FourNode.weightedMomentGramDet lambda x := by
  rw [MomentStability.unitMomentDet, FourNode.weightedMomentGramDet,
    FourNode.weightedMoment_zero]
  ring

/-- Explicit coefficientwise perturbation estimate.  Both determinant floors
are hypotheses because they are supplied uniformly on the compact valid
tail in the four-node application. -/
theorem arnoldiPoly2_coeffDist_principalWeights_le
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hv : ‖v‖ = 1)
    (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hfullDet : kappa ≤ momentGramDet A v)
    (hprincipalDet : kappa ≤ FourNode.weightedMomentGramDet
      (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
      (principalWeights A hA nodes v hcomponent)) :
    (arnoldiPoly2 A v).coeffDist
        (FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes v hcomponent)) ≤
      principalFactorPerturbationConstant A kappa *
        (2 * exteriorMass A hA nodes v * spectralMomentScale A) := by
  let lambda : Fin 4 → ℝ :=
    fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let x := principalWeights A hA nodes v hcomponent
  let B := eigenvalueAbsSum A
  let M := spectralMomentBound A
  let delta := 2 * exteriorMass A hA nodes v * spectralMomentScale A
  have hB : 0 ≤ B := eigenvalueAbsSum_nonneg A
  have hM : 0 ≤ M := spectralMomentBound_nonneg A
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (exteriorMass_nonneg A hA nodes v))
      (spectralMomentScale_nonneg A)
  have hpower_le (j : ℕ) (hj : j = 1 ∨ j = 2 ∨ j = 3) : B ^ j ≤ M := by
    rcases hj with rfl | rfl | rfl <;>
      dsimp only [M, spectralMomentBound, B] <;> nlinarith [sq_nonneg B, pow_nonneg hB 3]
  have hfull (j : ℕ) (hj : j = 1 ∨ j = 2 ∨ j = 3) :
      |moment A v j| ≤ M := by
    have h := abs_moment_le_eigenvalueAbsSum_pow_mul_norm_sq A hA v j
    rw [hv, one_pow, mul_one] at h
    exact h.trans (hpower_le j hj)
  have hprincipal (j : ℕ) (hj : j = 1 ∨ j = 2 ∨ j = 3) :
      |FourNode.weightedMoment lambda x j| ≤ M := by
    exact (abs_weightedMoment_principalWeights_le
      A hA nodes v hcomponent j).trans (hpower_le j hj)
  have hdiff (j : ℕ) (hj : j = 1 ∨ j = 2 ∨ j = 3) :
      |moment A v j - FourNode.weightedMoment lambda x j| ≤ delta := by
    have h := abs_moment_sub_weightedMoment_le
      A hA nodes hnodes v hv hcomponent j
    have hBj : B ^ j ≤ spectralMomentScale A := by
      rcases hj with rfl | rfl | rfl <;>
        dsimp only [spectralMomentScale, B] <;>
        nlinarith [sq_nonneg B, pow_nonneg hB 3]
    exact h.trans (mul_le_mul_of_nonneg_left hBj
      (mul_nonneg (by norm_num) (exteriorMass_nonneg A hA nodes v)))
  rw [arnoldiPoly2_eq_quadraticOfUnitMoments A v hv,
    FourNode.P_eq_quadraticOfUnitMoments]
  have hbound := MomentStability.coeffDist_quadraticOfUnitMoments_le
    hM hdelta hkappa
    (hfull 1 (Or.inl rfl)) (hfull 2 (Or.inr (Or.inl rfl)))
    (hfull 3 (Or.inr (Or.inr rfl)))
    (hprincipal 1 (Or.inl rfl)) (hprincipal 2 (Or.inr (Or.inl rfl)))
    (hprincipal 3 (Or.inr (Or.inr rfl)))
    (hdiff 1 (Or.inl rfl)) (hdiff 2 (Or.inr (Or.inl rfl)))
    (hdiff 3 (Or.inr (Or.inr rfl)))
    (by simpa [unitMomentDet_eq_momentGramDet A v hv] using hfullDet)
    (by simpa [FourNode.unitMomentDet_eq_weightedMomentGramDet lambda x]
      using hprincipalDet)
  simpa only [principalFactorPerturbationConstant, M, delta] using hbound

end

end Spectral
end Forsythe
