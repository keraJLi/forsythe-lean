import Forsythe.Main
import Forsythe.Matrix.Bridge

/-!
# Symmetric-matrix corollary

The matrix statement is the operator theorem transported through
`Matrix.toLpLin 2 2`.
-/

set_option autoImplicit false

namespace Matrix

open Filter Topology
open scoped ENNReal

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Forsythe's `s = 2` theorem for a real symmetric matrix acting on its
Euclidean coordinate space. -/
theorem forsythe_s2
    (A : Matrix n n ℝ) (hA : A.IsSymm)
    (v₀ : EuclideanSpace ℝ n) (hv₀ : ‖v₀‖ = 1)
    (hgrade : 3 ≤ Forsythe.Matrix.grade A v₀) :
    ∃ vEven vOdd,
      Tendsto (fun k ↦ Forsythe.Matrix.arnoldiOrbit2 A v₀ (2 * k))
        atTop (𝓝 vEven) ∧
      Tendsto (fun k ↦ Forsythe.Matrix.arnoldiOrbit2 A v₀ (2 * k + 1))
        atTop (𝓝 vOdd) := by
  exact Forsythe.forsythe_s2
    (Forsythe.Matrix.operator A)
    (Forsythe.Matrix.isSymmetric_operator hA) v₀ hv₀ hgrade

end

end Matrix
