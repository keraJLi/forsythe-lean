import Forsythe.Matrix.Main

/-!
# Compile-time regression checks for the public theorem API

These examples deliberately repeat the manuscript-facing operator and matrix
signatures.  They also pin the two Euclidean aliases used by the matrix
corollary to `Matrix.toLpLin 2 2`.
-/

set_option autoImplicit false

namespace ForsytheTest

open Filter Topology
open scoped ENNReal

noncomputable section

#check Forsythe.forsythe_s2
#check Matrix.forsythe_s2
#check Forsythe.Matrix.grade
#check Forsythe.Matrix.arnoldiOrbit2

/-- The operator theorem retains the exact manuscript-facing signature. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (v₀ : E) (hv₀ : ‖v₀‖ = 1)
    (hgrade : 3 ≤ Forsythe.grade A v₀) :
    ∃ vEven vOdd,
      Tendsto (fun k ↦ Forsythe.arnoldiOrbit2 A v₀ (2 * k))
        atTop (𝓝 vEven) ∧
      Tendsto (fun k ↦ Forsythe.arnoldiOrbit2 A v₀ (2 * k + 1))
        atTop (𝓝 vOdd) := by
  exact Forsythe.forsythe_s2 A hA v₀ hv₀ hgrade

/-- The matrix theorem retains the exact Euclidean-space signature. -/
example {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsSymm)
    (v₀ : EuclideanSpace ℝ n) (hv₀ : ‖v₀‖ = 1)
    (hgrade : 3 ≤ Forsythe.Matrix.grade A v₀) :
    ∃ vEven vOdd,
      Tendsto (fun k ↦ Forsythe.Matrix.arnoldiOrbit2 A v₀ (2 * k))
        atTop (𝓝 vEven) ∧
      Tendsto (fun k ↦ Forsythe.Matrix.arnoldiOrbit2 A v₀ (2 * k + 1))
        atTop (𝓝 vOdd) := by
  exact Matrix.forsythe_s2 A hA v₀ hv₀ hgrade

/-- The matrix grade is definitionally the operator grade after the
`Matrix.toLpLin 2 2` bridge. -/
example {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : EuclideanSpace ℝ n) :
    Forsythe.Matrix.grade A v =
      Forsythe.grade (Matrix.toLpLin 2 2 A) v := by
  rfl

/-- The matrix orbit is definitionally the operator orbit after the same
Euclidean bridge. -/
example {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v₀ : EuclideanSpace ℝ n) :
    Forsythe.Matrix.arnoldiOrbit2 A v₀ =
      Forsythe.arnoldiOrbit2 (Matrix.toLpLin 2 2 A) v₀ := by
  rfl

end

end ForsytheTest
