import Forsythe.Spectral.Coordinates
import Mathlib.Order.OrderIsoNat

/-!
# Stabilization of the active spectral components

Polynomial iteration can delete an eigenspace component but cannot recreate
it.  Since strict inclusion of finite active sets is well-founded, only
finitely many deletions can occur.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The active grouped eigenspaces form an antitone sequence. -/
theorem antitone_active_arnoldiOrbit2
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E) :
    Antitone fun k => active A hA (arnoldiOrbit2 A v₀ k) := by
  intro k l hkl
  exact active_arnoldiOrbit2_mono A hA v₀ hkl

/-- After a finite index, no further spectral component is deleted. -/
theorem exists_active_arnoldiOrbit2_stabilization
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E) :
    ∃ K : ℕ, ∀ l, K ≤ l →
      active A hA (arnoldiOrbit2 A v₀ l) =
        active A hA (arnoldiOrbit2 A v₀ K) := by
  obtain ⟨K, hK⟩ := WellFoundedLT.antitone_chain_condition
    (antitone_active_arnoldiOrbit2 A hA v₀)
  exact ⟨K, fun l hl => (hK l hl).symm⟩

/-- Bundled stabilization with a named finite set of surviving distinct
eigenvalues. -/
theorem exists_stable_active_spectrum
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E) :
    ∃ (K : ℕ) (S : Finset A.Eigenvalues),
      ∀ l, K ≤ l → active A hA (arnoldiOrbit2 A v₀ l) = S := by
  obtain ⟨K, hK⟩ := exists_active_arnoldiOrbit2_stabilization A hA v₀
  exact ⟨K, active A hA (arnoldiOrbit2 A v₀ K), hK⟩

/-- Every component in the stabilized active set stays nonzero throughout the
tail. -/
theorem component_ne_zero_of_mem_stable_active
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    {K : ℕ} {S : Finset A.Eigenvalues}
    (hstable : ∀ l, K ≤ l → active A hA (arnoldiOrbit2 A v₀ l) = S)
    {mu : A.Eigenvalues} (hmu : mu ∈ S) {l : ℕ} (hl : K ≤ l) :
    component A hA (arnoldiOrbit2 A v₀ l) mu ≠ 0 := by
  rw [← mem_active_iff A hA (arnoldiOrbit2 A v₀ l) mu]
  rw [hstable l hl]
  exact hmu

/-- Every component outside the stabilized active set is zero throughout the
tail. -/
theorem component_eq_zero_of_not_mem_stable_active
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    {K : ℕ} {S : Finset A.Eigenvalues}
    (hstable : ∀ l, K ≤ l → active A hA (arnoldiOrbit2 A v₀ l) = S)
    {mu : A.Eigenvalues} (hmu : mu ∉ S) {l : ℕ} (hl : K ≤ l) :
    component A hA (arnoldiOrbit2 A v₀ l) mu = 0 := by
  by_contra hne
  have hmem : mu ∈ active A hA (arnoldiOrbit2 A v₀ l) :=
    (mem_active_iff A hA (arnoldiOrbit2 A v₀ l) mu).2 hne
  rw [hstable l hl] at hmem
  exact hmu hmem

end

end Spectral
end Forsythe
