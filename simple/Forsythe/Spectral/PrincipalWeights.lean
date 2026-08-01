import Forsythe.FourNode.Weights
import Forsythe.Spectral.ComponentRecurrence

/-!
# Normalized four-node principal weights

This module connects grouped self-adjoint spectral coordinates with the
four-node simplex.  It records the normalized principal mass and proves the
exact normalized update driven by the ambient Arnoldi polynomial.  Exterior
components affect this identity only through the polynomial itself; no
asymptotic estimate is used here.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Total squared mass in four selected grouped eigenspaces. -/
def principalMass (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E) : ℝ :=
  ∑ i, weight A hA v (nodes i)

/-- A selected squared component normalized by the total selected mass. -/
def normalizedPrincipalWeight (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E) (i : Fin 4) : ℝ :=
  weight A hA v (nodes i) / principalMass A hA nodes v

theorem weight_nonneg (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) (mu : A.Eigenvalues) :
    0 ≤ weight A hA v mu := by
  exact sq_nonneg _

/-- Four nonzero selected components give strictly positive principal mass. -/
theorem principalMass_pos_of_components_ne_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0) :
    0 < principalMass A hA nodes v := by
  rw [principalMass]
  apply Finset.sum_pos'
  · intro i _
    exact weight_nonneg A hA v (nodes i)
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    rw [weight]
    exact sq_pos_of_pos (norm_pos_iff.mpr (hcomponent 0))

theorem sum_normalizedPrincipalWeight
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hmass : principalMass A hA nodes v ≠ 0) :
    ∑ i, normalizedPrincipalWeight A hA nodes v i = 1 := by
  simp only [normalizedPrincipalWeight]
  rw [← Finset.sum_div, principalMass]
  exact div_self hmass

theorem normalizedPrincipalWeight_nonneg
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hmass : 0 < principalMass A hA nodes v) (i : Fin 4) :
    0 ≤ normalizedPrincipalWeight A hA nodes v i := by
  exact div_nonneg (weight_nonneg A hA v (nodes i)) hmass.le

theorem normalizedPrincipalWeight_pos
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hmass : 0 < principalMass A hA nodes v)
    (i : Fin 4) (hcomponent : component A hA v (nodes i) ≠ 0) :
    0 < normalizedPrincipalWeight A hA nodes v i := by
  apply div_pos
  · rw [weight]
    exact sq_pos_of_pos (norm_pos_iff.mpr hcomponent)
  · exact hmass

/-- The normalized principal squared components as a four-node simplex
state.  Stable active components make all four entries positive, which is
stronger than the three-positive boundary condition in `FourNode.Weights`. -/
def principalWeights
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0) :
    FourNode.Weights where
  weight := normalizedPrincipalWeight A hA nodes v
  nonneg := normalizedPrincipalWeight_nonneg A hA nodes v
    (principalMass_pos_of_components_ne_zero A hA nodes v hcomponent)
  sum_eq_one := sum_normalizedPrincipalWeight A hA nodes v
    (ne_of_gt (principalMass_pos_of_components_ne_zero A hA nodes v hcomponent))
  three_le_card_positive := by
    have hall : ∀ i, 0 < normalizedPrincipalWeight A hA nodes v i :=
      fun i ↦ normalizedPrincipalWeight_pos A hA nodes v
        (principalMass_pos_of_components_ne_zero A hA nodes v hcomponent)
        i (hcomponent i)
    have heq : (Finset.univ.filter fun i ↦
        0 < normalizedPrincipalWeight A hA nodes v i) = Finset.univ := by
      exact Finset.filter_eq_self.2 fun i _ ↦ hall i
    rw [heq]
    norm_num

@[simp]
theorem principalWeights_apply
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0) (i : Fin 4) :
    principalWeights A hA nodes v hcomponent i =
      normalizedPrincipalWeight A hA nodes v i :=
  rfl

/-- The denominator in the normalized principal update, evaluated with an
arbitrary polynomial. -/
def normalizedPrincipalResidual
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E) (p : Polynomial ℝ) : ℝ :=
  ∑ i, normalizedPrincipalWeight A hA nodes v i *
    p.eval ((nodes i : A.Eigenvalues) : ℝ) ^ 2

/-- Exact normalized selected-weight update under one Arnoldi step. -/
theorem normalizedPrincipalWeight_arnoldiOrbit2_succ
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (k : ℕ)
    (hcomponent : ∀ i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    (hcomponentNext : ∀ i,
      component A hA (arnoldiOrbit2 A v₀ (k + 1)) (nodes i) ≠ 0)
    (i : Fin 4) :
    normalizedPrincipalWeight A hA nodes
        (arnoldiOrbit2 A v₀ (k + 1)) i =
      normalizedPrincipalWeight A hA nodes (arnoldiOrbit2 A v₀ k) i *
          (arnoldiFactorOrbit2 A v₀ k).toPolynomial.eval
            ((nodes i : A.Eigenvalues) : ℝ) ^ 2 /
        normalizedPrincipalResidual A hA nodes (arnoldiOrbit2 A v₀ k)
          (arnoldiFactorOrbit2 A v₀ k).toPolynomial := by
  let sigma := arnoldiNormalizerOrbit2 A v₀ k
  let p := (arnoldiFactorOrbit2 A v₀ k).toPolynomial
  let w : Fin 4 → ℝ := fun j ↦
    weight A hA (arnoldiOrbit2 A v₀ k) (nodes j)
  let M := principalMass A hA nodes (arnoldiOrbit2 A v₀ k)
  let R := ∑ j, w j * p.eval ((nodes j : A.Eigenvalues) : ℝ) ^ 2
  have hsigma : 0 < sigma :=
    (arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
      A hA v₀ hv₀ hgrade₀).sigma_pos k
  have hM : 0 < M :=
    principalMass_pos_of_components_ne_zero A hA nodes
      (arnoldiOrbit2 A v₀ k) hcomponent
  have hMnext : 0 < principalMass A hA nodes
      (arnoldiOrbit2 A v₀ (k + 1)) :=
    principalMass_pos_of_components_ne_zero A hA nodes
      (arnoldiOrbit2 A v₀ (k + 1)) hcomponentNext
  have hweight (j : Fin 4) :
      weight A hA (arnoldiOrbit2 A v₀ (k + 1)) (nodes j) =
        (sigma⁻¹ * p.eval ((nodes j : A.Eigenvalues) : ℝ)) ^ 2 * w j := by
    simpa only [sigma, p, w] using
      weight_arnoldiOrbit2_succ A hA v₀ (nodes j) k
  have hmassNext :
      principalMass A hA nodes (arnoldiOrbit2 A v₀ (k + 1)) =
        sigma⁻¹ ^ 2 * R := by
    rw [principalMass]
    simp_rw [hweight]
    dsimp only [R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w]
    ring
  have hresidual :
      normalizedPrincipalResidual A hA nodes (arnoldiOrbit2 A v₀ k) p =
        R / M := by
    rw [normalizedPrincipalResidual]
    simp only [normalizedPrincipalWeight]
    calc
      ∑ j, weight A hA (arnoldiOrbit2 A v₀ k) (nodes j) /
          principalMass A hA nodes (arnoldiOrbit2 A v₀ k) *
            p.eval ((nodes j : A.Eigenvalues) : ℝ) ^ 2 =
          ∑ j, (w j * p.eval ((nodes j : A.Eigenvalues) : ℝ) ^ 2) / M := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [M, w]
        ring
      _ = R / M := by
        rw [Finset.sum_div]
  have hR : R ≠ 0 := by
    intro hRzero
    rw [hRzero, mul_zero] at hmassNext
    exact (ne_of_gt hMnext) hmassNext
  rw [normalizedPrincipalWeight, hweight, hmassNext, hresidual]
  simp only [normalizedPrincipalWeight]
  change ((sigma⁻¹ * p.eval ((nodes i : A.Eigenvalues) : ℝ)) ^ 2 * w i) /
      (sigma⁻¹ ^ 2 * R) =
    (w i / M * p.eval ((nodes i : A.Eigenvalues) : ℝ) ^ 2) / (R / M)
  field_simp [ne_of_gt hsigma, ne_of_gt hM, hR]

end

end Spectral
end Forsythe
