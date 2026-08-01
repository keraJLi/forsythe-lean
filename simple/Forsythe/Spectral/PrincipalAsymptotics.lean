import Forsythe.Arnoldi.OrbitCoercivity
import Forsythe.Spectral.PrincipalPerturbation
import Forsythe.Spectral.PrincipalUpdatePerturbation

/-!
# Asymptotics of the normalized four-node principal problem

This module packages the denominator estimates used after exterior spectral
mass has been shown to vanish.  The four selected components are normalized
to a `FourNode.Weights` state.  Vanishing exterior mass then makes its first
moments, Gram determinant, and monic orthogonal quadratic asymptotic to their
ambient Arnoldi counterparts.  All comparison constants are explicit.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Topology
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A concrete common bound for a monic quadratic on the finite spectrum,
provided its pair of free coefficients has norm at most `M`. -/
def monicQuadraticSpectralEvalBound (A : Module.End ℝ E) (M : ℝ) : ℝ :=
  eigenvalueAbsSum A ^ 2 + M * eigenvalueAbsSum A + M

theorem monicQuadraticSpectralEvalBound_nonneg
    (A : Module.End ℝ E) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ monicQuadraticSpectralEvalBound A M := by
  exact add_nonneg
    (add_nonneg (sq_nonneg _) (mul_nonneg hM (eigenvalueAbsSum_nonneg A))) hM

/-- The coefficient-product norm gives an explicit simultaneous evaluation
bound at every eigenvalue. -/
theorem abs_monicQuadratic_eval_eigenvalue_le
    (A : Module.End ℝ E) (p : MonicQuadratic) {M : ℝ}
    (hM : 0 ≤ M) (hp : ‖p.coeffPair‖ ≤ M) (mu : A.Eigenvalues) :
    |p.toPolynomial.eval (mu : ℝ)| ≤
      monicQuadraticSpectralEvalBound A M := by
  let B := eigenvalueAbsSum A
  have hmu : |(mu : ℝ)| ≤ B := abs_eigenvalue_le_eigenvalueAbsSum A mu
  have ha : |p.linearCoeff| ≤ M :=
    (FourNode.abs_linearCoeff_le_coeffPair_norm_fourNode p).trans hp
  have hb : |p.constantCoeff| ≤ M :=
    (FourNode.abs_constantCoeff_le_coeffPair_norm_fourNode p).trans hp
  rw [MonicQuadratic.eval]
  calc
    |(mu : ℝ) ^ 2 + p.linearCoeff * (mu : ℝ) + p.constantCoeff| ≤
        |(mu : ℝ) ^ 2| + |p.linearCoeff * (mu : ℝ)| +
          |p.constantCoeff| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |(mu : ℝ)| ^ 2 + |p.linearCoeff| * |(mu : ℝ)| +
          |p.constantCoeff| := by rw [abs_pow, abs_mul]
    _ ≤ B ^ 2 + M * B + M := by
      exact add_le_add
        (add_le_add
          (pow_le_pow_left₀ (abs_nonneg (mu : ℝ)) hmu 2)
          (mul_le_mul ha hmu (abs_nonneg _) hM)) hb
    _ = monicQuadraticSpectralEvalBound A M := rfl

/-- The full polynomial residual and the residual normalized on four
selected eigenspaces differ by at most exterior mass times a concrete
spectral evaluation bound. -/
theorem abs_polyInner_sub_normalizedPrincipalResidual_le
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (v : E) (hv : ‖v‖ = 1)
    (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0)
    (p : MonicQuadratic) {M : ℝ} (hM : 0 ≤ M)
    (hp : ‖p.coeffPair‖ ≤ M) :
    |polyInner A v p.toPolynomial p.toPolynomial -
        normalizedPrincipalResidual A hA nodes v p.toPolynomial| ≤
      2 * exteriorMass A hA nodes v *
        monicQuadraticSpectralEvalBound A M ^ 2 := by
  let L := monicQuadraticSpectralEvalBound A M
  let mass := principalMass A hA nodes v
  let eps := exteriorMass A hA nodes v
  let R := normalizedPrincipalResidual A hA nodes v p.toPolynomial
  let selected := ∑ i, weight A hA v (nodes i) *
    p.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ) ^ 2
  let exterior := ∑ mu ∈ (Finset.univ : Finset A.Eigenvalues) with
    mu ∉ principalSpectrum A nodes,
      weight A hA v mu * p.toPolynomial.eval (mu : ℝ) ^ 2
  have hL : 0 ≤ L := monicQuadraticSpectralEvalBound_nonneg A hM
  have hmass : 0 < mass := by
    simpa only [mass] using
      principalMass_pos_of_components_ne_zero A hA nodes v hcomponent
  have heps : 0 ≤ eps := by
    simpa only [eps] using exteriorMass_nonneg A hA nodes v
  have heval (mu : A.Eigenvalues) :
      |p.toPolynomial.eval (mu : ℝ)| ≤ L := by
    simpa only [L] using abs_monicQuadratic_eval_eigenvalue_le A p hM hp mu
  have hselected : selected = mass * R := by
    dsimp only [selected, R, normalizedPrincipalResidual]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [normalizedPrincipalWeight]
    have hmassNe : principalMass A hA nodes v ≠ 0 := by
      exact ne_of_gt (principalMass_pos_of_components_ne_zero
        A hA nodes v hcomponent)
    field_simp [hmassNe]
    rfl
  have hfull :
      polyInner A v p.toPolynomial p.toPolynomial = selected + exterior := by
    rw [polyInner_eq_sum_weight_mul_eval_mul_eval A hA]
    have hprincipal :
        ∑ mu ∈ principalSpectrum A nodes,
            weight A hA v mu * p.toPolynomial.eval (mu : ℝ) *
              p.toPolynomial.eval (mu : ℝ) = selected := by
      rw [principalSpectrum, Finset.sum_image hnodes.injOn]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hpartition := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset A.Eigenvalues)
      (fun mu ↦ mu ∈ principalSpectrum A nodes)
      (fun mu ↦ weight A hA v mu * p.toPolynomial.eval (mu : ℝ) *
        p.toPolynomial.eval (mu : ℝ))
    have hfilter : (Finset.univ.filter fun mu : A.Eigenvalues ↦
        mu ∈ principalSpectrum A nodes) = principalSpectrum A nodes := by
      ext mu
      simp
    rw [hfilter] at hpartition
    rw [← hpartition, hprincipal]
    congr 1
    dsimp only [exterior]
    apply Finset.sum_congr rfl
    intro mu _
    ring
  have hmassEq : mass = 1 - eps := by
    simpa only [mass, eps] using
      principalMass_eq_one_sub_exteriorMass A hA nodes hnodes v hv
  have hRnonneg : 0 ≤ R := by
    dsimp only [R, normalizedPrincipalResidual]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg
      (normalizedPrincipalWeight_nonneg A hA nodes v hmass i) (sq_nonneg _)
  have hRle : R ≤ L ^ 2 := by
    dsimp only [R, normalizedPrincipalResidual]
    calc
      ∑ i, normalizedPrincipalWeight A hA nodes v i *
          p.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ) ^ 2 ≤
          ∑ i, normalizedPrincipalWeight A hA nodes v i * L ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            apply mul_le_mul_of_nonneg_left
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg _) hL).2 (heval (nodes i))
            exact normalizedPrincipalWeight_nonneg A hA nodes v hmass i
      _ = L ^ 2 := by
        rw [← Finset.sum_mul,
          sum_normalizedPrincipalWeight A hA nodes v (ne_of_gt hmass), one_mul]
  have hexteriorNonneg : 0 ≤ exterior := by
    dsimp only [exterior]
    exact Finset.sum_nonneg fun mu _ ↦
      mul_nonneg (weight_nonneg A hA v mu) (sq_nonneg _)
  have hexteriorLe : exterior ≤ eps * L ^ 2 := by
    dsimp only [exterior, eps, exteriorMass]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro mu hmu
    apply mul_le_mul_of_nonneg_left
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) hL).2 (heval mu)
    exact weight_nonneg A hA v mu
  have heq : polyInner A v p.toPolynomial p.toPolynomial - R =
      exterior - eps * R := by
    rw [hfull, hselected, hmassEq]
    ring
  rw [heq]
  calc
    |exterior - eps * R| ≤ |exterior| + |eps * R| := abs_sub _ _
    _ = exterior + eps * R := by
      rw [abs_of_nonneg hexteriorNonneg,
        abs_of_nonneg (mul_nonneg heps hRnonneg)]
    _ ≤ eps * L ^ 2 + eps * L ^ 2 :=
      add_le_add hexteriorLe (mul_le_mul_of_nonneg_left hRle heps)
    _ = 2 * eps * L ^ 2 := by ring
    _ = 2 * exteriorMass A hA nodes v *
        monicQuadraticSpectralEvalBound A M ^ 2 := rfl

/-- Vanishing exterior mass makes each fixed ambient moment asymptotic to
the corresponding moment of the normalized four-node principal weights. -/
theorem tendsto_abs_moment_sub_weightedMoment_principalWeights
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    (hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0)) (j : ℕ) :
    Tendsto (fun k ↦
      |moment A (arnoldiOrbit2 A v₀ k) j -
        FourNode.weightedMoment
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
            (hcomponent k)) j|)
      atTop (nhds 0) := by
  let eps : ℕ → ℝ := fun k ↦
    exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k)
  let B : ℝ := eigenvalueAbsSum A
  have heps : Tendsto eps atTop (nhds 0) := by
    simpa only [eps] using hext
  have hupper : Tendsto (fun k ↦ 2 * eps k * B ^ j)
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul heps).mul tendsto_const_nhds
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ abs_nonneg _
  · exact Eventually.of_forall fun k ↦ by
      simpa only [eps, B] using
        abs_moment_sub_weightedMoment_le A hA nodes hnodes
          (arnoldiOrbit2 A v₀ k)
          (norm_arnoldiOrbit2_of_initial_grade_three
            A hA v₀ hv₀ hgrade₀ k)
          (hcomponent k) j
  · exact hupper

/-- Signed form of
`tendsto_abs_moment_sub_weightedMoment_principalWeights`. -/
theorem tendsto_moment_sub_weightedMoment_principalWeights
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    (hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0)) (j : ℕ) :
    Tendsto (fun k ↦
      moment A (arnoldiOrbit2 A v₀ k) j -
        FourNode.weightedMoment
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
            (hcomponent k)) j)
      atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  exact tendsto_abs_moment_sub_weightedMoment_principalWeights
    A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext j

/-- The weighted four-node moment Gram determinant differs from the full
moment Gram determinant by a quantity tending to zero. -/
theorem tendsto_weightedMomentGramDet_sub_momentGramDet
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    (hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0)) :
    Tendsto (fun k ↦
      FourNode.weightedMomentGramDet
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
            (hcomponent k)) -
        momentGramDet A (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0) := by
  let lambda : Fin 4 → ℝ :=
    fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let v : ℕ → E := fun k ↦ arnoldiOrbit2 A v₀ k
  let x : ℕ → FourNode.Weights := fun k ↦
    principalWeights A hA nodes (v k) (hcomponent k)
  let m₁ : ℕ → ℝ := fun k ↦ moment A (v k) 1
  let m₂ : ℕ → ℝ := fun k ↦ moment A (v k) 2
  let n₁ : ℕ → ℝ := fun k ↦ FourNode.weightedMoment lambda (x k) 1
  let n₂ : ℕ → ℝ := fun k ↦ FourNode.weightedMoment lambda (x k) 2
  let B : ℝ := eigenvalueAbsSum A
  have hnorm : ∀ k, ‖v k‖ = 1 := by
    intro k
    exact norm_arnoldiOrbit2_of_initial_grade_three
      A hA v₀ hv₀ hgrade₀ k
  have hdiff₁ : Tendsto (fun k ↦ |m₁ k - n₁ k|) atTop (nhds 0) := by
    simpa only [m₁, n₁, v, x, lambda] using
      tendsto_abs_moment_sub_weightedMoment_principalWeights
        A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext 1
  have hdiff₂ : Tendsto (fun k ↦ |m₂ k - n₂ k|) atTop (nhds 0) := by
    simpa only [m₂, n₂, v, x, lambda] using
      tendsto_abs_moment_sub_weightedMoment_principalWeights
        A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext 2
  have hupper : Tendsto
      (fun k ↦ |m₂ k - n₂ k| + 2 * B * |m₁ k - n₁ k|)
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      hdiff₂.add ((tendsto_const_nhds.mul tendsto_const_nhds).mul hdiff₁)
  have hbound : ∀ k,
      |FourNode.weightedMomentGramDet lambda (x k) -
          momentGramDet A (v k)| ≤
        |m₂ k - n₂ k| + 2 * B * |m₁ k - n₁ k| := by
    intro k
    have hm₁ : |m₁ k| ≤ B := by
      have h := abs_moment_le_eigenvalueAbsSum_pow_mul_norm_sq
        A hA (v k) 1
      simpa only [pow_one, hnorm k, one_pow, mul_one, m₁, B] using h
    have hn₁ : |n₁ k| ≤ B := by
      simpa only [pow_one, n₁, B, lambda, x, v] using
        abs_weightedMoment_principalWeights_le
          A hA nodes (v k) (hcomponent k) 1
    have hsq : |n₁ k ^ 2 - m₁ k ^ 2| ≤
        2 * B * |m₁ k - n₁ k| := by
      rw [show n₁ k ^ 2 - m₁ k ^ 2 =
          (n₁ k - m₁ k) * (n₁ k + m₁ k) by ring,
        abs_mul, abs_sub_comm]
      calc
        |m₁ k - n₁ k| * |n₁ k + m₁ k| ≤
            |m₁ k - n₁ k| * (2 * B) := by
              apply mul_le_mul_of_nonneg_left
              exact (abs_add_le _ _).trans (by linarith)
              exact abs_nonneg _
        _ = 2 * B * |m₁ k - n₁ k| := by ring
    have hfull : momentGramDet A (v k) = m₂ k - m₁ k ^ 2 := by
      rw [momentGramDet, moment_zero, real_inner_self_eq_norm_sq, hnorm k]
      simp only [one_pow, one_mul, m₁, m₂]
    have hprincipal : FourNode.weightedMomentGramDet lambda (x k) =
        n₂ k - n₁ k ^ 2 := by
      rw [FourNode.weightedMomentGramDet, FourNode.weightedMoment_zero]
      simp only [one_mul, n₁, n₂]
    rw [hfull, hprincipal]
    calc
      |(n₂ k - n₁ k ^ 2) - (m₂ k - m₁ k ^ 2)| ≤
          |n₂ k - m₂ k| + |n₁ k ^ 2 - m₁ k ^ 2| := by
            have heq : (n₂ k - n₁ k ^ 2) - (m₂ k - m₁ k ^ 2) =
                (n₂ k - m₂ k) - (n₁ k ^ 2 - m₁ k ^ 2) := by ring
            rw [heq]
            exact abs_sub _ _
      _ ≤ |m₂ k - n₂ k| + 2 * B * |m₁ k - n₁ k| := by
        rw [abs_sub_comm (n₂ k) (m₂ k)]
        exact add_le_add (le_refl _) hsq
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  change Tendsto (fun k ↦
    |FourNode.weightedMomentGramDet
        (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
        (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
          (hcomponent k)) -
      momentGramDet A (arnoldiOrbit2 A v₀ k)|) atTop (nhds 0)
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ abs_nonneg _
  · simpa only [lambda, x, v] using Eventually.of_forall hbound
  · exact hupper

/-- A valid orbit with vanishing exterior mass has one common positive tail
floor for both the ambient and normalized-principal moment Gram systems. -/
theorem exists_eventually_common_momentGramDet_lower_bound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    (hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0)) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ k in atTop,
        kappa ≤ momentGramDet A (arnoldiOrbit2 A v₀ k) ∧
        kappa ≤ FourNode.weightedMomentGramDet
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
            (hcomponent k)) := by
  obtain ⟨kappa₀, hkappa₀, hfull⟩ :=
    exists_eventually_arnoldiOrbit2_momentGramDet_lower_bound
      A hA v₀ hv₀ hgrade₀
  let kappa : ℝ := kappa₀ / 2
  have hkappa : 0 < kappa := by dsimp only [kappa]; linarith
  have hdiff := tendsto_weightedMomentGramDet_sub_momentGramDet
    A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext
  have hdiffAbs : Tendsto (fun k ↦
      |FourNode.weightedMomentGramDet
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
            (hcomponent k)) -
        momentGramDet A (arnoldiOrbit2 A v₀ k)|)
      atTop (nhds 0) := by
    simpa only [abs_zero] using hdiff.abs
  have hsmall : ∀ᶠ k in atTop,
      |FourNode.weightedMomentGramDet
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
            (hcomponent k)) -
        momentGramDet A (arnoldiOrbit2 A v₀ k)| < kappa := by
    exact (tendsto_order.1 hdiffAbs).2 kappa hkappa
  refine ⟨kappa, hkappa, ?_⟩
  filter_upwards [hfull, hsmall] with k hfullK hsmallK
  constructor
  · dsimp only [kappa]
    linarith
  · have hlower := neg_lt_of_abs_lt hsmallK
    dsimp only [kappa] at hlower ⊢
    linarith

/-- Explicit tail comparison between the ambient Arnoldi factor and the
intrinsic factor of the normalized principal weights. -/
theorem exists_eventually_arnoldiFactor_coeffDist_principalWeights_le
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    (hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0)) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ k in atTop,
        (arnoldiFactorOrbit2 A v₀ k).coeffDist
            (FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
              (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
                (hcomponent k))) ≤
          principalFactorPerturbationConstant A kappa *
            (2 * exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k) *
              spectralMomentScale A) := by
  obtain ⟨kappa, hkappa, hfloors⟩ :=
    exists_eventually_common_momentGramDet_lower_bound
      A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext
  refine ⟨kappa, hkappa, ?_⟩
  filter_upwards [hfloors] with k hk
  simpa only [arnoldiFactorOrbit2] using
    arnoldiPoly2_coeffDist_principalWeights_le
      A hA nodes hnodes (arnoldiOrbit2 A v₀ k)
      (norm_arnoldiOrbit2_of_initial_grade_three
        A hA v₀ hv₀ hgrade₀ k)
      (hcomponent k) kappa hkappa hk.1 hk.2

/-- In particular, vanishing exterior mass forces the ambient and intrinsic
quadratic factors to have vanishing coefficient distance. -/
theorem tendsto_arnoldiFactor_coeffDist_principalWeights
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    (hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0)) :
    Tendsto (fun k ↦
      (arnoldiFactorOrbit2 A v₀ k).coeffDist
        (FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
            (hcomponent k))))
      atTop (nhds 0) := by
  obtain ⟨kappa, hkappa, hbound⟩ :=
    exists_eventually_arnoldiFactor_coeffDist_principalWeights_le
      A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext
  let C : ℝ := principalFactorPerturbationConstant A kappa
  let S : ℝ := spectralMomentScale A
  let eps : ℕ → ℝ := fun k ↦
    exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k)
  have heps : Tendsto eps atTop (nhds 0) := by simpa only [eps] using hext
  have hupper : Tendsto (fun k ↦ C * (2 * eps k * S))
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      tendsto_const_nhds.mul
        ((tendsto_const_nhds.mul heps).mul tendsto_const_nhds)
  apply squeeze_zero'
  · exact Eventually.of_forall fun k ↦ MonicQuadratic.coeffDist_nonneg _ _
  · simpa only [C, S, eps] using hbound
  · exact hupper

/-- A geometric exterior-mass estimate gives a geometric coefficient
estimate for the ambient-versus-intrinsic four-node factor defect. -/
theorem exists_eventually_arnoldiFactor_coeffDist_principalWeights_geometric
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    {C theta : ℝ} (hC : 0 ≤ C) (hthetaNonneg : 0 ≤ theta)
    (htheta : theta < 1)
    (hextGeometric : ∀ᶠ k in atTop,
      exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k) ≤ C * theta ^ k) :
    ∃ kappa Cfactor : ℝ, 0 < kappa ∧ 0 ≤ Cfactor ∧
      ∀ᶠ k in atTop,
        (arnoldiFactorOrbit2 A v₀ k).coeffDist
            (FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
              (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
                (hcomponent k))) ≤ Cfactor * theta ^ k := by
  have hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun k ↦ exteriorMass_nonneg A hA nodes _
    · exact hextGeometric
    · simpa only [mul_zero] using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hthetaNonneg htheta)
  obtain ⟨kappa, hkappa, hfactor⟩ :=
    exists_eventually_arnoldiFactor_coeffDist_principalWeights_le
      A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext
  let Cfactor := principalFactorPerturbationConstant A kappa *
    (2 * C * spectralMomentScale A)
  have hperturb : 0 ≤ principalFactorPerturbationConstant A kappa := by
    have hM := spectralMomentBound_nonneg A
    dsimp only [principalFactorPerturbationConstant]
    positivity
  have hCfactor : 0 ≤ Cfactor := by
    dsimp only [Cfactor]
    exact mul_nonneg hperturb
      (mul_nonneg (mul_nonneg (by norm_num) hC)
        (spectralMomentScale_nonneg A))
  refine ⟨kappa, Cfactor, hkappa, hCfactor, ?_⟩
  filter_upwards [hfactor, hextGeometric] with k hfactorK hextK
  calc
    (arnoldiFactorOrbit2 A v₀ k).coeffDist
        (FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
            (hcomponent k))) ≤
        principalFactorPerturbationConstant A kappa *
          (2 * exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k) *
            spectralMomentScale A) := hfactorK
    _ ≤ principalFactorPerturbationConstant A kappa *
          (2 * (C * theta ^ k) * spectralMomentScale A) := by
      apply mul_le_mul_of_nonneg_left _ hperturb
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hextK (by norm_num))
        (spectralMomentScale_nonneg A)
    _ = Cfactor * theta ^ k := by
      dsimp only [Cfactor]
      ring

/-- Once the ambient Arnoldi coefficients are bounded, exterior-mass decay
identifies the normalized principal residual with the squared Arnoldi
normalizer in the limit. -/
theorem tendsto_normalizedPrincipalResidual_arnoldiOrbit2
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    {tau M : ℝ} (hM : 0 ≤ M)
    (hcoeff : ∀ᶠ k in atTop,
      ‖(arnoldiFactorOrbit2 A v₀ k).coeffPair‖ ≤ M)
    (hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0))
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau)) :
    Tendsto (fun k ↦ normalizedPrincipalResidual A hA nodes
        (arnoldiOrbit2 A v₀ k)
        (arnoldiFactorOrbit2 A v₀ k).toPolynomial)
      atTop (nhds (tau ^ 2)) := by
  let sigma := arnoldiNormalizerOrbit2 A v₀
  let R : ℕ → ℝ := fun k ↦ normalizedPrincipalResidual A hA nodes
    (arnoldiOrbit2 A v₀ k) (arnoldiFactorOrbit2 A v₀ k).toPolynomial
  let L := monicQuadraticSpectralEvalBound A M
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  have hupper : Tendsto (fun k ↦
      2 * exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k) * L ^ 2)
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hext).mul tendsto_const_nhds
  have hdiffAbs : Tendsto (fun k ↦ |sigma k ^ 2 - R k|)
      atTop (nhds 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun _ ↦ abs_nonneg _)
      (hcoeff.mono fun k hk ↦ by
        have hbound := abs_polyInner_sub_normalizedPrincipalResidual_le
          A hA nodes hnodes (arnoldiOrbit2 A v₀ k)
          (norm_arnoldiOrbit2_of_initial_grade_three
            A hA v₀ hv₀ hgrade₀ k)
          (hcomponent k) (arnoldiFactorOrbit2 A v₀ k) hM hk
        rw [(hsteps.step k).norm_sq] at hbound
        simpa only [sigma, R, L] using hbound)
      hupper
  have hdiff : Tendsto (fun k ↦ sigma k ^ 2 - R k)
      atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 hdiffAbs
  have hsigmaSq : Tendsto (fun k ↦ sigma k ^ 2)
      atTop (nhds (tau ^ 2)) := by
    simpa only [sigma, pow_two] using hnormalizer.mul hnormalizer
  have ht : Tendsto (fun k ↦ sigma k ^ 2 - (sigma k ^ 2 - R k))
      atTop (nhds (tau ^ 2)) := by
    simpa only [sub_zero] using hsigmaSq.sub hdiff
  simpa only [R] using ht.congr'
    (Eventually.of_forall fun k ↦ by ring)

/-- Comparing two quadratic residuals on the same normalized four-node
weights costs at most coefficient distance times an explicit evaluation
constant. -/
theorem abs_normalizedPrincipalResidual_sub_H_le
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues)
    (v : E) (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0)
    (p : MonicQuadratic) {L : ℝ}
    (hpEval : ∀ i,
      |p.toPolynomial.eval ((nodes i : A.Eigenvalues) : ℝ)| ≤ L)
    (hPEval : ∀ i,
      |(FourNode.P (fun j ↦ ((nodes j : A.Eigenvalues) : ℝ))
        (principalWeights A hA nodes v hcomponent)).toPolynomial.eval
          ((nodes i : A.Eigenvalues) : ℝ)| ≤ L) :
    |normalizedPrincipalResidual A hA nodes v p.toPolynomial -
        FourNode.H (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
          (principalWeights A hA nodes v hcomponent)| ≤
      2 * L *
        (FourNode.nodeRadius
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + 1) *
        p.coeffDist
          (FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
            (principalWeights A hA nodes v hcomponent)) := by
  let lambda : Fin 4 → ℝ :=
    fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let x := principalWeights A hA nodes v hcomponent
  let q := FourNode.P lambda x
  let d := p.coeffDist q
  have hd : 0 ≤ d := MonicQuadratic.coeffDist_nonneg _ _
  rw [normalizedPrincipalResidual, FourNode.H, FourNode.height,
    FourNode.weightedPolyInner]
  change |∑ i, x i * p.toPolynomial.eval (lambda i) ^ 2 -
      ∑ i, x i * q.toPolynomial.eval (lambda i) *
        q.toPolynomial.eval (lambda i)| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (x i * p.toPolynomial.eval (lambda i) ^ 2 -
        x i * q.toPolynomial.eval (lambda i) *
          q.toPolynomial.eval (lambda i))| ≤
        ∑ i, |x i * (p.toPolynomial.eval (lambda i) ^ 2 -
          q.toPolynomial.eval (lambda i) ^ 2)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            ring
    _ ≤ ∑ i, x i *
        (2 * L * (FourNode.nodeRadius lambda + 1) * d) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (x.nonneg i)]
      apply mul_le_mul_of_nonneg_left _ (x.nonneg i)
      rw [show p.toPolynomial.eval (lambda i) ^ 2 -
          q.toPolynomial.eval (lambda i) ^ 2 =
        (p.toPolynomial.eval (lambda i) - q.toPolynomial.eval (lambda i)) *
          (p.toPolynomial.eval (lambda i) + q.toPolynomial.eval (lambda i)) by ring,
        abs_mul]
      calc
        |p.toPolynomial.eval (lambda i) - q.toPolynomial.eval (lambda i)| *
            |p.toPolynomial.eval (lambda i) + q.toPolynomial.eval (lambda i)| ≤
            ((FourNode.nodeRadius lambda + 1) * d) * (2 * L) := by
              apply mul_le_mul
              · exact abs_monicQuadratic_eval_sub_le_nodeRadius lambda p q i
              · exact (abs_add_le _ _).trans (by
                  dsimp only [lambda, q, x]
                  linarith [hpEval i, hPEval i])
              · exact abs_nonneg _
              · exact mul_nonneg
                  (add_nonneg (FourNode.nodeRadius_nonneg lambda) (by norm_num)) hd
        _ = 2 * L * (FourNode.nodeRadius lambda + 1) * d := by ring
    _ = 2 * L * (FourNode.nodeRadius lambda + 1) * d := by
      rw [← Finset.sum_mul, x.sum_eq_one, one_mul]
    _ = 2 * L *
        (FourNode.nodeRadius
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + 1) *
        p.coeffDist
          (FourNode.P (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
            (principalWeights A hA nodes v hcomponent)) := rfl

/-- Along a valid orbit, vanishing exterior mass and convergence of the
ambient normalizer force the intrinsic four-node height to converge to the
same squared limit.  The required ambient coefficient bound is supplied
internally by orbit coercivity. -/
theorem tendsto_principalWeights_H_arnoldiOrbit2
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    {tau : ℝ}
    (hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0))
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau)) :
    Tendsto (fun k ↦
      FourNode.H (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
        (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
          (hcomponent k)))
      atTop (nhds (tau ^ 2)) := by
  let lambda : Fin 4 → ℝ :=
    fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let x : ℕ → FourNode.Weights := fun k ↦
    principalWeights A hA nodes (arnoldiOrbit2 A v₀ k) (hcomponent k)
  let p : ℕ → MonicQuadratic := arnoldiFactorOrbit2 A v₀
  let q : ℕ → MonicQuadratic := fun k ↦ FourNode.P lambda (x k)
  let d : ℕ → ℝ := fun k ↦ (p k).coeffDist (q k)
  let R : ℕ → ℝ := fun k ↦ normalizedPrincipalResidual A hA nodes
    (arnoldiOrbit2 A v₀ k) (p k).toPolynomial
  let H : ℕ → ℝ := fun k ↦ FourNode.H lambda (x k)
  obtain ⟨M, hM, hpBound⟩ :=
    exists_eventually_arnoldiFactorOrbit2_coeffPair_bound
      A hA v₀ hv₀ hgrade₀
  have hR : Tendsto R atTop (nhds (tau ^ 2)) := by
    simpa only [R, p] using
      tendsto_normalizedPrincipalResidual_arnoldiOrbit2
        A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hM hpBound
        hext hnormalizer
  have hd : Tendsto d atTop (nhds 0) := by
    simpa only [d, p, q, lambda, x] using
      tendsto_arnoldiFactor_coeffDist_principalWeights
        A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext
  have hdOne : ∀ᶠ k in atTop, d k < 1 :=
    (tendsto_order.1 hd).2 1 zero_lt_one
  let M₁ := M + 1
  let L := monicQuadraticSpectralEvalBound A M₁
  let Cres := 2 * L * (FourNode.nodeRadius lambda + 1)
  have hM₁ : 0 ≤ M₁ := by dsimp only [M₁]; linarith
  have hbounds : ∀ᶠ k in atTop,
      ‖(p k).coeffPair‖ ≤ M₁ ∧ ‖(q k).coeffPair‖ ≤ M₁ := by
    filter_upwards [hpBound, hdOne] with k hpK hdK
    have hqDistance : ‖(q k).coeffPair - (p k).coeffPair‖ = d k := by
      rw [norm_sub_rev]
      rfl
    constructor
    · dsimp only [M₁]
      linarith
    · calc
        ‖(q k).coeffPair‖ ≤
            ‖(p k).coeffPair‖ + ‖(q k).coeffPair - (p k).coeffPair‖ :=
          norm_le_norm_add_norm_sub' _ _
        _ = ‖(p k).coeffPair‖ + d k := by rw [hqDistance]
        _ ≤ M₁ := by dsimp only [M₁]; linarith
  have hupper : Tendsto (fun k ↦ Cres * d k) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hd
  have hdiffAbs : Tendsto (fun k ↦ |R k - H k|) atTop (nhds 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun _ ↦ abs_nonneg _)
      (hbounds.mono fun k hk ↦ by
        have hpEval (i : Fin 4) :
            |(p k).toPolynomial.eval (lambda i)| ≤ L := by
          simpa only [L, lambda] using
            abs_monicQuadratic_eval_eigenvalue_le A (p k) hM₁ hk.1 (nodes i)
        have hqEval (i : Fin 4) :
            |(q k).toPolynomial.eval (lambda i)| ≤ L := by
          simpa only [L, lambda] using
            abs_monicQuadratic_eval_eigenvalue_le A (q k) hM₁ hk.2 (nodes i)
        have hbound := abs_normalizedPrincipalResidual_sub_H_le
          A hA nodes (arnoldiOrbit2 A v₀ k) (hcomponent k) (p k)
          hpEval (by simpa only [q, lambda, x] using hqEval)
        simpa only [R, H, p, q, x, lambda, Cres, d] using hbound)
      hupper
  have hdiff : Tendsto (fun k ↦ R k - H k) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 hdiffAbs
  have ht : Tendsto (fun k ↦ R k - (R k - H k))
      atTop (nhds (tau ^ 2)) := by
    simpa only [sub_zero] using hR.sub hdiff
  simpa only [H, lambda, x] using ht.congr'
    (Eventually.of_forall fun k ↦ by ring)

/-- If the limiting normalizer is positive, the intrinsic four-node height
has a common positive lower bound on an orbit tail. -/
theorem exists_eventually_principalWeights_H_lower_bound
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    {tau : ℝ} (htau : 0 < tau)
    (hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0))
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau)) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ k in atTop,
      eta ≤ FourNode.H (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
        (principalWeights A hA nodes (arnoldiOrbit2 A v₀ k)
          (hcomponent k)) := by
  let eta := tau ^ 2 / 2
  have htauSq : 0 < tau ^ 2 := sq_pos_of_pos htau
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hH := tendsto_principalWeights_H_arnoldiOrbit2
    A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext hnormalizer
  refine ⟨eta, heta, ?_⟩
  exact ((tendsto_order.1 hH).1 eta (by dsimp only [eta]; linarith)).mono
    fun _ hk ↦ hk.le

/-- Quantitative operator-to-four-node reduction: geometric exterior decay
implies that the actual normalized principal-weight update is a geometric
perturbation of the exact four-node map. -/
theorem exists_eventually_principalWeights_updateDefect_geometric
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (nodes : Fin 4 → A.Eigenvalues) (hnodes : Function.Injective nodes)
    (hcomponent : ∀ k i,
      component A hA (arnoldiOrbit2 A v₀ k) (nodes i) ≠ 0)
    {tau C theta : ℝ} (htau : 0 < tau) (hC : 0 ≤ C)
    (hthetaNonneg : 0 ≤ theta) (htheta : theta < 1)
    (hextGeometric : ∀ᶠ k in atTop,
      exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k) ≤ C * theta ^ k)
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau)) :
    ∃ Cupdate : ℝ, 0 ≤ Cupdate ∧ ∀ᶠ k in atTop,
      ‖FourNode.weightVector
          (principalWeights A hA nodes
            (arnoldiOrbit2 A v₀ (k + 1)) (hcomponent (k + 1))) -
        FourNode.weightVector
          (FourNode.T (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
            (fun _ _ hij ↦ hnodes (Subtype.ext hij))
            (principalWeights A hA nodes
              (arnoldiOrbit2 A v₀ k) (hcomponent k)))‖ ≤
        Cupdate * theta ^ k := by
  let lambda : Fin 4 → ℝ :=
    fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)
  let x : ℕ → FourNode.Weights := fun k ↦
    principalWeights A hA nodes (arnoldiOrbit2 A v₀ k) (hcomponent k)
  let p : ℕ → MonicQuadratic := arnoldiFactorOrbit2 A v₀
  let q : ℕ → MonicQuadratic := fun k ↦ FourNode.P lambda (x k)
  let d : ℕ → ℝ := fun k ↦ (p k).coeffDist (q k)
  let R : ℕ → ℝ := fun k ↦ normalizedPrincipalResidual A hA nodes
    (arnoldiOrbit2 A v₀ k) (p k).toPolynomial
  let H : ℕ → ℝ := fun k ↦ FourNode.H lambda (x k)
  have hext : Tendsto
      (fun k ↦ exteriorMass A hA nodes (arnoldiOrbit2 A v₀ k))
      atTop (nhds 0) := by
    have hupper : Tendsto (fun k : ℕ ↦ C * theta ^ k)
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hthetaNonneg htheta)
    exact squeeze_zero'
      (Eventually.of_forall fun _ ↦ exteriorMass_nonneg A hA nodes _)
      hextGeometric
      hupper
  obtain ⟨_, Cfactor, _, hCfactor, hfactor⟩ :=
    exists_eventually_arnoldiFactor_coeffDist_principalWeights_geometric
      A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hC hthetaNonneg
      htheta hextGeometric
  obtain ⟨M, hM, hpBound⟩ :=
    exists_eventually_arnoldiFactorOrbit2_coeffPair_bound
      A hA v₀ hv₀ hgrade₀
  have hd : Tendsto d atTop (nhds 0) := by
    simpa only [d, p, q, lambda, x] using
      tendsto_arnoldiFactor_coeffDist_principalWeights
        A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext
  have hdOne : ∀ᶠ k in atTop, d k < 1 :=
    (tendsto_order.1 hd).2 1 zero_lt_one
  let M₁ := M + 1
  let L := monicQuadraticSpectralEvalBound A M₁
  have hM₁ : 0 ≤ M₁ := by dsimp only [M₁]; linarith
  have hL : 0 ≤ L := by
    exact monicQuadraticSpectralEvalBound_nonneg A hM₁
  have hbounds : ∀ᶠ k in atTop,
      ‖(p k).coeffPair‖ ≤ M₁ ∧ ‖(q k).coeffPair‖ ≤ M₁ := by
    filter_upwards [hpBound, hdOne] with k hpK hdK
    have hqDistance : ‖(q k).coeffPair - (p k).coeffPair‖ = d k := by
      rw [norm_sub_rev]
      rfl
    constructor
    · dsimp only [M₁]
      linarith
    · calc
        ‖(q k).coeffPair‖ ≤
            ‖(p k).coeffPair‖ + ‖(q k).coeffPair - (p k).coeffPair‖ :=
          norm_le_norm_add_norm_sub' _ _
        _ = ‖(p k).coeffPair‖ + d k := by rw [hqDistance]
        _ ≤ M₁ := by dsimp only [M₁]; linarith
  have hRlimit : Tendsto R atTop (nhds (tau ^ 2)) := by
    simpa only [R, p] using
      tendsto_normalizedPrincipalResidual_arnoldiOrbit2
        A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hM hpBound
        hext hnormalizer
  have hHlimit : Tendsto H atTop (nhds (tau ^ 2)) := by
    simpa only [H, lambda, x] using
      tendsto_principalWeights_H_arnoldiOrbit2
        A hA v₀ hv₀ hgrade₀ nodes hnodes hcomponent hext hnormalizer
  let eta := tau ^ 2 / 2
  have htauSq : 0 < tau ^ 2 := sq_pos_of_pos htau
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hRFloor : ∀ᶠ k in atTop, eta ≤ R k :=
    ((tendsto_order.1 hRlimit).1 eta (by dsimp only [eta]; linarith)).mono
      fun _ hk ↦ hk.le
  have hHFloor : ∀ᶠ k in atTop, eta ≤ H k :=
    ((tendsto_order.1 hHlimit).1 eta (by dsimp only [eta]; linarith)).mono
      fun _ hk ↦ hk.le
  let Cupdate :=
    principalUpdatePolynomialLipschitzConstant lambda L eta * Cfactor
  have hLip : 0 ≤
      principalUpdatePolynomialLipschitzConstant lambda L eta :=
    principalUpdatePolynomialLipschitzConstant_nonneg lambda hL heta
  have hCupdate : 0 ≤ Cupdate := by
    exact mul_nonneg hLip hCfactor
  refine ⟨Cupdate, hCupdate, ?_⟩
  filter_upwards [hfactor, hbounds, hRFloor, hHFloor]
    with k hfactorK hboundK hRK hHK
  have hpEval (i : Fin 4) : |(p k).toPolynomial.eval (lambda i)| ≤ L := by
    simpa only [L, lambda] using
      abs_monicQuadratic_eval_eigenvalue_le A (p k) hM₁ hboundK.1 (nodes i)
  have hqEval (i : Fin 4) : |(q k).toPolynomial.eval (lambda i)| ≤ L := by
    simpa only [L, lambda] using
      abs_monicQuadratic_eval_eigenvalue_le A (q k) hM₁ hboundK.2 (nodes i)
  have hstep := principalWeights_succ_sub_T_norm_le
    A hA v₀ hv₀ hgrade₀ nodes hnodes k (hcomponent k)
      (hcomponent (k + 1)) hL heta
      (by simpa only [p, lambda] using hpEval)
      (by simpa only [q, lambda, x] using hqEval)
      (by simpa only [R, p] using hRK)
      (by simpa only [H, lambda, x] using hHK)
  calc
    ‖FourNode.weightVector
          (principalWeights A hA nodes
            (arnoldiOrbit2 A v₀ (k + 1)) (hcomponent (k + 1))) -
        FourNode.weightVector
          (FourNode.T (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
            (fun _ _ hij ↦ hnodes (Subtype.ext hij))
            (principalWeights A hA nodes
              (arnoldiOrbit2 A v₀ k) (hcomponent k)))‖ ≤
        principalUpdatePolynomialLipschitzConstant lambda L eta * d k := by
          simpa only [lambda, x, p, q, d] using hstep
    _ ≤ principalUpdatePolynomialLipschitzConstant lambda L eta *
        (Cfactor * theta ^ k) :=
      mul_le_mul_of_nonneg_left (by simpa only [d, p, q, lambda, x] using hfactorK)
        hLip
    _ = Cupdate * theta ^ k := by dsimp only [Cupdate]; ring

end

end Spectral
end Forsythe
