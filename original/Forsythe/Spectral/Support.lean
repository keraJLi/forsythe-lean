import Forsythe.Spectral.Grade
import Mathlib.Algebra.Polynomial.Roots

/-!
# Spectral support bounds from polynomial annihilators

An annihilating polynomial must vanish at every active distinct eigenvalue.
Counting its distinct roots therefore bounds intrinsic grade.  The main
specialization is the manuscript polynomial `p q - H`, where `p` and `q` are
monic quadratics, hence the annihilator is a monic quartic.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Module.End Polynomial

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- If a nonzero polynomial annihilates `v`, every active distinct eigenvalue
is one of its roots. -/
theorem active_image_subset_roots_of_polyApply_eq_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (r : Polynomial ℝ) (hr : r ≠ 0)
    (hann : polyApply A r v = 0) :
    (active A hA v).image (fun mu : A.Eigenvalues ↦ (mu : ℝ)) ⊆
      r.roots.toFinset := by
  classical
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨mu, hmu, rfl⟩ := hx
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hr, Polynomial.IsRoot]
  have hcomponent := congrArg (fun w : E ↦ component A hA w mu) hann
  rw [component_polyApply] at hcomponent
  have hzero : component A hA (0 : E) mu = 0 := by
    simp [component]
  rw [hzero] at hcomponent
  exact (smul_eq_zero.mp hcomponent).resolve_right
    ((mem_active_iff A hA v mu).mp hmu)

/-- The number of active distinct eigenvalues is bounded by the degree of any
nonzero annihilating polynomial. -/
theorem active_card_le_natDegree_of_polyApply_eq_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (r : Polynomial ℝ) (hr : r ≠ 0)
    (hann : polyApply A r v = 0) :
    (active A hA v).card ≤ r.natDegree := by
  classical
  let imageActive : Finset ℝ :=
    (active A hA v).image (fun mu : A.Eigenvalues ↦ (mu : ℝ))
  have hcard : imageActive.card = (active A hA v).card := by
    exact Finset.card_image_of_injective _ Subtype.coe_injective
  calc
    (active A hA v).card = imageActive.card := hcard.symm
    _ ≤ r.roots.toFinset.card := Finset.card_le_card
      (active_image_subset_roots_of_polyApply_eq_zero A hA v r hr hann)
    _ ≤ r.roots.card := Multiset.toFinset_card_le r.roots
    _ ≤ r.natDegree := Polynomial.card_roots' r

/-- Intrinsic grade form of the polynomial-annihilator bound. -/
theorem grade_le_natDegree_of_polyApply_eq_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (r : Polynomial ℝ) (hr : r ≠ 0)
    (hann : polyApply A r v = 0) :
    grade A v ≤ r.natDegree := by
  rw [grade_eq_card_active A hA v]
  exact active_card_le_natDegree_of_polyApply_eq_zero A hA v r hr hann

/-- A monic quadratic has natural degree two. -/
@[simp]
theorem natDegree_monicQuadratic (p : MonicQuadratic) :
    p.toPolynomial.natDegree = 2 := by
  have hle : p.toPolynomial.natDegree ≤ 2 := by
    rw [MonicQuadratic.toPolynomial]
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · simp
      · simpa only [pow_one] using
          (natDegree_C_mul_X_pow_le p.linearCoeff 1).trans (by norm_num : 1 ≤ 2)
    · simp
  have hge : 2 ≤ p.toPolynomial.natDegree :=
    le_natDegree_of_ne_zero (by simp)
  exact le_antisymm hle hge

/-- The shifted product of two monic quadratics is a monic quartic. -/
theorem monic_quadraticProduct_sub_C
    (p q : MonicQuadratic) (H : ℝ) :
    (p.toPolynomial * q.toPolynomial - C H).Monic := by
  have hpqMonic : (p.toPolynomial * q.toPolynomial).Monic :=
    (MonicQuadratic.monic p).mul (MonicQuadratic.monic q)
  apply hpqMonic.sub_of_left
  rw [degree_eq_natDegree hpqMonic.ne_zero,
    (MonicQuadratic.monic p).natDegree_mul (MonicQuadratic.monic q),
    natDegree_monicQuadratic, natDegree_monicQuadratic]
  exact lt_of_le_of_lt degree_C_le (by norm_num)

/-- Natural-degree form of `monic_quadraticProduct_sub_C`. -/
theorem natDegree_quadraticProduct_sub_C
    (p q : MonicQuadratic) (H : ℝ) :
    (p.toPolynomial * q.toPolynomial - C H).natDegree = 4 := by
  rw [natDegree_sub_C,
    (MonicQuadratic.monic p).natDegree_mul (MonicQuadratic.monic q),
    natDegree_monicQuadratic, natDegree_monicQuadratic]

/-- A grade-at-least-three vector annihilated by a monic quartic has exactly
three or four active distinct eigenvalues. -/
theorem active_card_eq_three_or_four_of_monic_quartic_annihilator
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (r : Polynomial ℝ) (hrMonic : r.Monic) (hrDegree : r.natDegree = 4)
    (hgrade : 3 ≤ grade A v) (hann : polyApply A r v = 0) :
    (active A hA v).card = 3 ∨ (active A hA v).card = 4 := by
  have hlower : 3 ≤ (active A hA v).card := by
    rwa [← grade_eq_card_active A hA v]
  have hupper := active_card_le_natDegree_of_polyApply_eq_zero
    A hA v r hrMonic.ne_zero hann
  rw [hrDegree] at hupper
  omega

/-- Manuscript form: if `(p q - H)` annihilates a grade-at-least-three
state, then its grouped spectral support has cardinality three or four. -/
theorem active_card_eq_three_or_four_of_quadraticProduct_sub_C_annihilator
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (p q : MonicQuadratic) (H : ℝ)
    (hgrade : 3 ≤ grade A v)
    (hann : polyApply A (p.toPolynomial * q.toPolynomial - C H) v = 0) :
    (active A hA v).card = 3 ∨ (active A hA v).card = 4 := by
  exact active_card_eq_three_or_four_of_monic_quartic_annihilator
    A hA v (p.toPolynomial * q.toPolynomial - C H)
      (monic_quadraticProduct_sub_C p q H)
      (natDegree_quadraticProduct_sub_C p q H) hgrade hann

end

end Spectral
end Forsythe
