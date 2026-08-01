import Forsythe.Arnoldi.MomentGram
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Low-degree annihilators and the grade

The elementary Krylov argument in this file avoids spectral coordinates.  A
monic quadratic annihilating `v` makes the span of `v, A v` invariant, hence
forces the cyclic subspace to have dimension at most two.
-/

set_option autoImplicit false

namespace Forsythe

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first two Krylov vectors. -/
def krylov2 (A : Module.End ℝ E) (v : E) : Submodule ℝ E :=
  Submodule.span ℝ ({v, A v} : Set E)

theorem mem_krylov2_self (A : Module.End ℝ E) (v : E) :
    v ∈ krylov2 A v := by
  exact Submodule.subset_span (by simp)

theorem mem_krylov2_apply (A : Module.End ℝ E) (v : E) :
    A v ∈ krylov2 A v := by
  exact Submodule.subset_span (by simp)

/-- If a monic quadratic annihilates `v`, then the first-two-vector Krylov
span is invariant under `A`. -/
theorem krylov2_apply_mem_of_monicQuadratic_apply_eq_zero
    (A : Module.End ℝ E) (p : MonicQuadratic) (v x : E)
    (hann : polyApply A p.toPolynomial v = 0)
    (hx : x ∈ krylov2 A v) :
    A x ∈ krylov2 A v := by
  have hA2 :
      A (A v) = (-p.linearCoeff) • A v + (-p.constantCoeff) • v := by
    rw [polyApply_monicQuadratic A v p] at hann
    simp only [pow_two, Module.End.mul_apply] at hann
    have hsum :
        A (A v) + (p.linearCoeff • A v + p.constantCoeff • v) = 0 := by
      simpa [add_assoc] using hann
    calc
      A (A v) = -(p.linearCoeff • A v + p.constantCoeff • v) :=
        eq_neg_of_add_eq_zero_left hsum
      _ = (-p.linearCoeff) • A v + (-p.constantCoeff) • v := by
        simp [add_comm]
  refine Submodule.span_induction
    (p := fun y _ => A y ∈ krylov2 A v) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact mem_krylov2_apply A v
    · rw [hy, hA2]
      exact (krylov2 A v).add_mem
        ((krylov2 A v).smul_mem _ (mem_krylov2_apply A v))
        ((krylov2 A v).smul_mem _ (mem_krylov2_self A v))
  · rw [map_zero]
    exact (krylov2 A v).zero_mem
  · intro y z _ _ hy hz
    rw [map_add]
    exact (krylov2 A v).add_mem hy hz
  · intro c y _ hy
    rw [map_smul]
    exact (krylov2 A v).smul_mem c hy

/-- Every Krylov power lies in the first-two-vector span when a monic
quadratic annihilates the starting vector. -/
theorem pow_apply_mem_krylov2_of_monicQuadratic_apply_eq_zero
    (A : Module.End ℝ E) (p : MonicQuadratic) (v : E)
    (hann : polyApply A p.toPolynomial v = 0) :
    ∀ k : ℕ, (A ^ k) v ∈ krylov2 A v := by
  intro k
  induction k with
  | zero => simpa using mem_krylov2_self A v
  | succ k ih =>
      simpa [pow_succ'] using
        krylov2_apply_mem_of_monicQuadratic_apply_eq_zero A p v _ hann ih

theorem cyclicSubspace_le_krylov2_of_monicQuadratic_apply_eq_zero
    (A : Module.End ℝ E) (p : MonicQuadratic) (v : E)
    (hann : polyApply A p.toPolynomial v = 0) :
    cyclicSubspace A v ≤ krylov2 A v := by
  rw [cyclicSubspace]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact pow_apply_mem_krylov2_of_monicQuadratic_apply_eq_zero A p v hann k

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- A monic quadratic annihilator forces grade at most two. -/
theorem grade_le_two_of_monicQuadratic_apply_eq_zero
    (A : Module.End ℝ E) (p : MonicQuadratic) (v : E)
    (hann : polyApply A p.toPolynomial v = 0) :
    grade A v ≤ 2 := by
  classical
  have hle := cyclicSubspace_le_krylov2_of_monicQuadratic_apply_eq_zero
    A p v hann
  have hmono :
      Module.finrank ℝ (cyclicSubspace A v) ≤
        Module.finrank ℝ (krylov2 A v) :=
    Submodule.finrank_mono hle
  let s : Finset E := {v, A v}
  have hspan := finrank_span_finset_le_card (R := ℝ) s
  change Module.finrank ℝ (Submodule.span ℝ (s : Set E)) ≤ s.card at hspan
  have hcard : s.card ≤ 2 := Finset.card_le_two
  have hs : (s : Set E) = {v, A v} := by
    ext x
    simp [s]
  have hkrylov : Module.finrank ℝ (krylov2 A v) ≤ s.card := by
    rw [krylov2, ← hs]
    exact hspan
  exact hmono.trans (hkrylov.trans hcard)

/-- Grade at least three rules out every monic quadratic annihilator. -/
theorem monicQuadratic_apply_ne_zero_of_grade_ge_three
    (A : Module.End ℝ E) (p : MonicQuadratic) (v : E)
    (hgrade : 3 ≤ grade A v) :
    polyApply A p.toPolynomial v ≠ 0 := by
  intro hann
  have hle := grade_le_two_of_monicQuadratic_apply_eq_zero A p v hann
  omega

/-- In particular, a grade-three state has a nonzero raw Arnoldi update. -/
theorem rawArnoldiStep2_ne_zero_of_grade_ge_three
    (A : Module.End ℝ E) (v : E) (hgrade : 3 ≤ grade A v) :
    rawArnoldiStep2 A v ≠ 0 := by
  exact monicQuadratic_apply_ne_zero_of_grade_ge_three A
    (arnoldiPoly2 A v) v hgrade

end FiniteDimensional

end
end Forsythe
