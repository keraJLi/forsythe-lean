import Forsythe.Arnoldi.Defs
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Bridge from real symmetric matrices to self-adjoint operators

The theorem-facing matrix corollary uses `Matrix.toLpLin 2 2`, whose domain is
the real Euclidean space on the matrix index type.  Real matrix symmetry is
exactly symmetry of this linear endomorphism.
-/

set_option autoImplicit false

namespace Forsythe
namespace Matrix

open scoped ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable section

/-- The Euclidean linear operator associated with a square real matrix. -/
abbrev operator (A : _root_.Matrix n n ℝ) :
    Module.End ℝ (EuclideanSpace ℝ n) :=
  _root_.Matrix.toLpLin 2 2 A

/-- A real symmetric matrix gives a self-adjoint Euclidean operator. -/
theorem isSymmetric_operator {A : _root_.Matrix n n ℝ}
    (hA : A.IsSymm) : (operator A).IsSymmetric := by
  change A.toEuclideanLin.IsSymmetric
  apply _root_.Matrix.isSymmetric_toEuclideanLin_iff.mpr
  exact _root_.Matrix.isHermitian_iff_isSymm.mpr hA

/-- Matrix-facing grade, defined through the Euclidean operator bridge. -/
abbrev grade (A : _root_.Matrix n n ℝ) (v : EuclideanSpace ℝ n) : ℕ :=
  Forsythe.grade (operator A) v

/-- Matrix-facing restart-two Arnoldi orbit. -/
abbrev arnoldiOrbit2 (A : _root_.Matrix n n ℝ)
    (v₀ : EuclideanSpace ℝ n) : ℕ → EuclideanSpace ℝ n :=
  Forsythe.arnoldiOrbit2 (operator A) v₀

end

end Matrix
end Forsythe
