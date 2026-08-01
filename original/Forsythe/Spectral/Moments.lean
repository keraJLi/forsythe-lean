import Forsythe.Spectral.ComponentRecurrence
import Forsythe.Spectral.PrincipalWeights

/-!
# Polynomial orthogonality in grouped spectral coordinates

After the intrinsic Arnoldi development, the self-adjoint eigenbasis turns
The polynomial form becomes a finite weighted sum over distinct active
eigenvalues.  Repeated eigenvalues remain grouped in a single squared norm.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Polynomial
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Spectral-coordinate formula for the polynomial inner product. -/
theorem polyInner_eq_sum_weight_mul_eval_mul_eval
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E)
    (p q : Polynomial ℝ) :
    polyInner A v p q =
      ∑ mu : A.Eigenvalues, weight A hA v mu *
        p.eval (mu : ℝ) * q.eval (mu : ℝ) := by
  rw [polyInner, ← hA.diagonalization.inner_map_map, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro mu _
  change inner ℝ
      (component A hA (polyApply A p v) mu)
      (component A hA (polyApply A q v) mu) = _
  rw [component_polyApply, component_polyApply]
  simp only [real_inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, weight]
  ring

/-- The `k`th moment is the finite weighted power sum of the grouped
eigenvalues. -/
theorem moment_eq_sum_weight_mul_pow
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v : E) (k : ℕ) :
    moment A v k =
      ∑ mu : A.Eigenvalues, weight A hA v mu * (mu : ℝ) ^ k := by
  have h := polyInner_eq_sum_weight_mul_eval_mul_eval
    A hA v (X ^ k) 1
  simpa [moment, polyInner, polyApply] using h

/-- The selected normalized four-node moment is the selected unnormalized
moment divided by the principal mass. -/
theorem weightedMoment_principalWeights
    (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (nodes : Fin 4 → A.Eigenvalues) (v : E)
    (hcomponent : ∀ i, component A hA v (nodes i) ≠ 0) (k : ℕ) :
    FourNode.weightedMoment
        (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))
        (principalWeights A hA nodes v hcomponent) k =
      (∑ i, weight A hA v (nodes i) *
        ((nodes i : A.Eigenvalues) : ℝ) ^ k) /
        principalMass A hA nodes v := by
  rw [FourNode.weightedMoment]
  simp only [principalWeights_apply, normalizedPrincipalWeight]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end

end Spectral
end Forsythe
