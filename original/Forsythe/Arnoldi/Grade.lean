import Forsythe.Arnoldi.Cyclic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Preservation of the grade

The proof is intrinsic to the polynomial orthogonality form.  If the
updated vector had grade at most two, it would have a monic quadratic
annihilator.  Its two-vector Krylov space would then be invariant.  The
Arnoldi orthogonality equations make the old vector orthogonal to this space,
while symmetry moves the Arnoldi factor across the inner product and forces
the raw update to have zero norm.
-/

set_option autoImplicit false

namespace Forsythe

open Polynomial

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mem_cyclicSubspace_self (A : Module.End ℝ E) (v : E) :
    v ∈ cyclicSubspace A v := by
  rw [cyclicSubspace]
  apply Submodule.subset_span
  exact ⟨0, by simp⟩

theorem mem_cyclicSubspace_apply (A : Module.End ℝ E) (v : E) :
    A v ∈ cyclicSubspace A v := by
  rw [cyclicSubspace]
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

theorem krylov2_le_cyclicSubspace (A : Module.End ℝ E) (v : E) :
    krylov2 A v ≤ cyclicSubspace A v := by
  rw [krylov2]
  apply Submodule.span_le.2
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · subst x
    exact mem_cyclicSubspace_self A v
  · subst x
    exact mem_cyclicSubspace_apply A v

/-- Every state of grade at most two admits a monic quadratic annihilator.
This is the elementary two-vector Krylov version of the minimal-polynomial
fact needed by grade preservation. -/
theorem exists_monicQuadratic_apply_eq_zero_of_grade_le_two
    (A : Module.End ℝ E) (v : E) [FiniteDimensional ℝ E]
    (hgrade : grade A v ≤ 2) :
    ∃ p : MonicQuadratic, polyApply A p.toPolynomial v = 0 := by
  by_cases hv : v = 0
  · let p : MonicQuadratic := ⟨0, 0⟩
    refine ⟨p, ?_⟩
    subst v
    simp [polyApply_monicQuadratic]
  by_cases hli : LinearIndependent ℝ ![v, A v]
  · have hrange : Set.range ![v, A v] = ({v, A v} : Set E) := by
      ext x
      simp [or_comm]
    have hkfin : Module.finrank ℝ (krylov2 A v) = 2 := by
      rw [krylov2, ← hrange, finrank_span_eq_card hli]
      simp
    have hk_eq : krylov2 A v = cyclicSubspace A v := by
      apply Submodule.eq_of_le_of_finrank_le (krylov2_le_cyclicSubspace A v)
      rw [hkfin]
      exact hgrade
    have hA2 : (A ^ 2) v ∈ krylov2 A v := by
      rw [hk_eq, cyclicSubspace]
      apply Submodule.subset_span
      exact ⟨2, rfl⟩
    rw [krylov2, Submodule.mem_span_pair] at hA2
    obtain ⟨a, b, hab⟩ := hA2
    let p : MonicQuadratic := ⟨-b, -a⟩
    refine ⟨p, ?_⟩
    rw [polyApply_monicQuadratic]
    change (A ^ 2) v + (-b) • A v + (-a) • v = 0
    rw [← hab]
    module
  · rw [LinearIndependent.pair_iff' hv] at hli
    push Not at hli
    obtain ⟨c, hc⟩ := hli
    have hA2 : (A ^ 2) v = c • A v := by
      calc
        (A ^ 2) v = A (A v) := by simp [pow_two, Module.End.mul_apply]
        _ = A (c • v) := by rw [hc]
        _ = c • A v := map_smul A c v
    let p : MonicQuadratic := ⟨-c, 0⟩
    refine ⟨p, ?_⟩
    rw [polyApply_monicQuadratic]
    change (A ^ 2) v + (-c) • A v + (0 : ℝ) • v = 0
    rw [hA2]
    simp

/-- A vector orthogonal to the first two Krylov vectors is orthogonal to their
whole span. -/
theorem inner_eq_zero_of_mem_krylov2 (A : Module.End ℝ E) (v w x : E)
    (hvw : inner ℝ v w = 0) (hvAw : inner ℝ v (A w) = 0)
    (hx : x ∈ krylov2 A w) : inner ℝ v x = 0 := by
  rw [krylov2, Submodule.mem_span_pair] at hx
  obtain ⟨a, b, rfl⟩ := hx
  simp [inner_add_right, real_inner_smul_right, hvw, hvAw]

/-- Once `q` annihilates `w`, the two-vector Krylov span is invariant and
therefore contains the action of every monic quadratic on `w`. -/
theorem polyApply_monicQuadratic_mem_krylov2_of_annihilator
    (A : Module.End ℝ E) (q p : MonicQuadratic) (w : E)
    (hq : polyApply A q.toPolynomial w = 0) :
    polyApply A p.toPolynomial w ∈ krylov2 A w := by
  have hA2 := krylov2_apply_mem_of_monicQuadratic_apply_eq_zero
    A q w (A w) hq (mem_krylov2_apply A w)
  rw [polyApply_monicQuadratic]
  apply (krylov2 A w).add_mem
  · apply (krylov2 A w).add_mem
    · simpa [pow_two, Module.End.mul_apply] using hA2
    · exact (krylov2 A w).smul_mem _ (mem_krylov2_apply A w)
  · exact (krylov2 A w).smul_mem _ (mem_krylov2_self A w)

/-- No monic quadratic can annihilate the normalized update of a grade-three
state.  The proof uses only Arnoldi orthogonality, invariance of a
two-dimensional Krylov space, and symmetry of polynomial action. -/
theorem monicQuadratic_apply_arnoldiStep2_ne_zero_of_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional ℝ E] (hgrade : 3 ≤ grade A v)
    (q : MonicQuadratic) :
    polyApply A q.toPolynomial (arnoldiStep2 A v) ≠ 0 := by
  intro hqstep
  let p := arnoldiPoly2 A v
  let w := rawArnoldiStep2 A v
  have hw_ne : w ≠ 0 := by
    exact rawArnoldiStep2_ne_zero_of_grade_ge_three A v hgrade
  have hscale_ne : ‖w‖⁻¹ ≠ 0 :=
    inv_ne_zero (norm_ne_zero_iff.mpr hw_ne)
  have hqw : polyApply A q.toPolynomial w = 0 := by
    change polyApply A q.toPolynomial (‖w‖⁻¹ • w) = 0 at hqstep
    rw [polyApply_smul] at hqstep
    exact (smul_eq_zero.mp hqstep).resolve_left hscale_ne
  have hp1 := arnoldiPoly2_orthogonal_one A hA v hgrade
  have hpX := arnoldiPoly2_orthogonal_X A hA v hgrade
  have hwv : inner ℝ w v = 0 := by
    simpa only [w, rawArnoldiStep2, polyInner, polyApply_one] using hp1
  have hwAv : inner ℝ w (A v) = 0 := by
    simpa only [w, rawArnoldiStep2, polyInner, polyApply_X] using hpX
  have hvw : inner ℝ v w = 0 := by
    rw [real_inner_comm]
    exact hwv
  have hvAw : inner ℝ v (A w) = 0 := by
    calc
      inner ℝ v (A w) = inner ℝ (A w) v := real_inner_comm _ _
      _ = inner ℝ w (A v) := hA w v
      _ = 0 := hwAv
  have hpw_mem : polyApply A p.toPolynomial w ∈ krylov2 A w :=
    polyApply_monicQuadratic_mem_krylov2_of_annihilator A q p w hqw
  have hnorm_zero : inner ℝ w w = 0 := by
    calc
      inner ℝ w w = inner ℝ (polyApply A p.toPolynomial v) w := by
        rfl
      _ = inner ℝ v (polyApply A p.toPolynomial w) := by
        simpa only [polyApply] using
          (polynomial_aeval_isSymmetric A hA p.toPolynomial v w)
      _ = 0 := inner_eq_zero_of_mem_krylov2 A v w _ hvw hvAw hpw_mem
  exact hw_ne ((inner_self_eq_zero (𝕜 := ℝ)).mp hnorm_zero)

/-- A restart-two Arnoldi step preserves the lower grade bound. -/
theorem grade_arnoldiStep2_of_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional ℝ E] (hgrade : 3 ≤ grade A v) :
    3 ≤ grade A (arnoldiStep2 A v) := by
  by_contra hnot
  have hle : grade A (arnoldiStep2 A v) ≤ 2 := by omega
  obtain ⟨q, hq⟩ :=
    exists_monicQuadratic_apply_eq_zero_of_grade_le_two
      A (arnoldiStep2 A v) hle
  exact monicQuadratic_apply_arnoldiStep2_ne_zero_of_grade_three
    A hA v hgrade q hq

/-- The grade-three invariant propagates along the entire Arnoldi orbit. -/
theorem grade_arnoldiOrbit2_of_grade_three
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    [FiniteDimensional ℝ E] (hgrade₀ : 3 ≤ grade A v₀) :
    ∀ k : ℕ, 3 ≤ grade A (arnoldiOrbit2 A v₀ k) := by
  intro k
  induction k with
  | zero => simpa using hgrade₀
  | succ k ih =>
      rw [arnoldiOrbit2_succ]
      exact grade_arnoldiStep2_of_grade_three A hA _ ih

end

end Forsythe
