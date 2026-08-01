import Forsythe.FourNode.Interpolation

/-! Regression checks at a genuine three-positive four-node boundary state. -/

set_option autoImplicit false

namespace ForsytheTest

open Forsythe
open Forsythe.FourNode

noncomputable section

private def boundaryNodes (i : Fin 4) : ℝ := i.1

private theorem boundaryNodes_injective : Function.Injective boundaryNodes := by
  intro i j hij
  apply Fin.ext
  simp only [boundaryNodes] at hij
  exact_mod_cast hij

private def boundaryWeights : Weights where
  weight := ![(1 : ℝ) / 3, 1 / 3, 1 / 3, 0]
  nonneg := by
    intro i
    fin_cases i <;> norm_num
  sum_eq_one := by
    simp [Fin.sum_univ_four]
    norm_num
  three_le_card_positive := by
    have heq : (Finset.univ.filter fun i : Fin 4 ↦
        0 < (![((1 : ℝ) / 3), 1 / 3, 1 / 3, 0] i)) = Finset.univ.erase 3 := by
      ext i
      fin_cases i <;> simp
    rw [heq]
    simp

example : (positiveSupport boundaryWeights).card = 3 := by
  have heq : positiveSupport boundaryWeights = Finset.univ.erase 3 := by
    ext i
    fin_cases i <;> simp [positiveSupport, boundaryWeights]
  rw [heq]
  simp

example : 3 ≤ (positiveSupport
    (T boundaryNodes boundaryNodes_injective boundaryWeights)).card :=
  three_le_card_positiveSupport _

example :
    (P boundaryNodes boundaryWeights).toPolynomial *
        (P boundaryNodes
          (T boundaryNodes boundaryNodes_injective boundaryWeights)).toPolynomial =
      nodalQuartic boundaryNodes +
        Polynomial.C (H boundaryNodes
          (T boundaryNodes boundaryNodes_injective boundaryWeights)) +
        alpha boundaryNodes boundaryNodes_injective boundaryWeights •
          dividedDifference boundaryNodes (rho boundaryNodes boundaryWeights) :=
  interpolation_identity boundaryNodes_injective boundaryWeights

example :
    rho boundaryNodes
        (T boundaryNodes boundaryNodes_injective boundaryWeights) -
          rho boundaryNodes boundaryWeights =
      alpha boundaryNodes boundaryNodes_injective boundaryWeights *
          (nodalQuartic boundaryNodes).eval (rho boundaryNodes boundaryWeights) /
        H boundaryNodes
          (T boundaryNodes boundaryNodes_injective boundaryWeights) :=
  rho_T_sub_rho boundaryNodes_injective boundaryWeights

end
end ForsytheTest
