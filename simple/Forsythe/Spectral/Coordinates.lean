import Forsythe.Arnoldi.Foundation
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral coordinates for a self-adjoint operator

We use mathlib's orthogonal direct sum of the *distinct* eigenspaces.  Thus an
index records an eigenvalue, rather than an eigenvector in a chosen basis, and
repeated eigenvalues are grouped from the outset.  This is the internal
coordinate model used after the theorem-facing, orthogonality-based Arnoldi
development.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Module.End WithLp

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The component of `v` in the eigenspace indexed by the distinct eigenvalue
`mu`. -/
def component (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (mu : A.Eigenvalues) : eigenspace A (mu : ℝ) :=
  hA.diagonalization v mu

/-- The finite set of distinct eigenspaces in which `v` has a nonzero
component. -/
def active (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E) :
    Finset A.Eigenvalues := by
  classical
  exact Finset.univ.filter fun mu => component A hA v mu ≠ 0

@[simp]
theorem mem_active_iff (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) (mu : A.Eigenvalues) :
    mu ∈ active A hA v ↔ component A hA v mu ≠ 0 := by
  classical
  simp [active]

/-- Spectral coordinates are isometric. -/
theorem norm_component_family (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (v : E) :
    ‖hA.diagonalization v‖ = ‖v‖ :=
  hA.diagonalization.norm_map v

/-- Polynomial action is scalar evaluation on every grouped eigenspace
component. -/
theorem component_polyApply (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (p : Polynomial ℝ) (v : E) (mu : A.Eigenvalues) :
    component A hA (polyApply A p v) mu =
      p.eval (mu : ℝ) • component A hA v mu := by
  revert v mu
  refine p.induction_on ?_ ?_ ?_
  · intro a v mu
    simp [component, polyApply, Module.algebraMap_end_apply]
  · intro p q hp hq v mu
    have happly : polyApply A (p + q) v =
        polyApply A p v + polyApply A q v := by
      simp [polyApply]
    rw [happly]
    have hcomponent : component A hA
        (polyApply A p v + polyApply A q v) mu =
        component A hA (polyApply A p v) mu +
          component A hA (polyApply A q v) mu := by
      simp [component]
    rw [hcomponent]
    rw [hp, hq, Polynomial.eval_add, add_smul]
  · intro n a ih v mu
    rw [pow_succ, ← mul_assoc, polyApply_mul]
    rw [show polyApply A Polynomial.X v = A v by simp [polyApply]]
    rw [ih]
    have hcomponentA : component A hA (A v) mu =
        (mu : ℝ) • component A hA v mu := by
      exact hA.diagonalization_apply_self_apply v mu
    rw [hcomponentA]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, smul_smul]

/-- A polynomial cannot create a component in an eigenspace where the input
component vanished. -/
theorem component_polyApply_eq_zero_of_eq_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (p : Polynomial ℝ) (v : E) (mu : A.Eigenvalues)
    (hzero : component A hA v mu = 0) :
    component A hA (polyApply A p v) mu = 0 := by
  rw [component_polyApply, hzero, smul_zero]

/-- Exact component formula for one normalized Arnoldi step. -/
theorem component_arnoldiStep2
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (mu : A.Eigenvalues) :
    component A hA (arnoldiStep2 A v) mu =
      (‖rawArnoldiStep2 A v‖⁻¹ *
        (arnoldiPoly2 A v).toPolynomial.eval (mu : ℝ)) •
          component A hA v mu := by
  rw [arnoldiStep2]
  unfold component
  rw [map_smul, PiLp.smul_apply]
  change ‖rawArnoldiStep2 A v‖⁻¹ •
      component A hA
        (polyApply A (arnoldiPoly2 A v).toPolynomial v) mu = _
  rw [component_polyApply]
  rw [smul_smul]
  rfl

/-- Once a spectral component has been deleted, one Arnoldi step cannot
recreate it. -/
theorem component_arnoldiStep2_eq_zero_of_eq_zero
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (mu : A.Eigenvalues) (hzero : component A hA v mu = 0) :
    component A hA (arnoldiStep2 A v) mu = 0 := by
  rw [component_arnoldiStep2, hzero, smul_zero]

/-- A component absent at one orbit index is absent at every later index. -/
theorem component_arnoldiOrbit2_eq_zero_of_le
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (mu : A.Eigenvalues) {k l : ℕ} (hkl : k ≤ l)
    (hzero : component A hA (arnoldiOrbit2 A v₀ k) mu = 0) :
    component A hA (arnoldiOrbit2 A v₀ l) mu = 0 := by
  induction l, hkl using Nat.le_induction with
  | base => exact hzero
  | succ l _ ih =>
      rw [arnoldiOrbit2_succ]
      exact component_arnoldiStep2_eq_zero_of_eq_zero A hA _ mu ih

/-- Active distinct eigenspaces can only be deleted along the orbit. -/
theorem active_arnoldiOrbit2_mono
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    {k l : ℕ} (hkl : k ≤ l) :
    active A hA (arnoldiOrbit2 A v₀ l) ⊆
      active A hA (arnoldiOrbit2 A v₀ k) := by
  intro mu hmu
  rw [mem_active_iff] at hmu ⊢
  contrapose! hmu
  exact component_arnoldiOrbit2_eq_zero_of_le A hA v₀ mu hkl hmu

end

end Spectral
end Forsythe
