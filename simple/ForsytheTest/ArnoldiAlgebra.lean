import Forsythe.Arnoldi.Algebra
import Forsythe.Arnoldi.Variation

/-! Compile-time checks for the manuscript-facing Stage 1 identities. -/

set_option autoImplicit false

namespace ForsytheTest

open Forsythe

#check Forsythe.polyInner_transport
#check Forsythe.quadraticStep_transport
#check Forsythe.quadraticStep_transport_two
#check Forsythe.quadraticStep_energy
#check Forsythe.quadraticStep_correlation
#check Forsythe.quadraticStep_cancellation
#check Forsythe.quadraticStep_three_step
#check Forsythe.Arnoldi.factor_variation_of_coercive

private def p : MonicQuadratic := ⟨2, 3⟩
private def q : MonicQuadratic := ⟨2, 3⟩

example : p.coeffDist q ≤ (4 : ℝ) * 0 := by
  apply Forsythe.Arnoldi.factor_variation_of_coercive p q 1 4 4 0 0
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [p, MonicQuadratic.coeffPair]
  · norm_num [q, MonicQuadratic.coeffPair]
  · norm_num [MonicQuadratic.coeffDist, p, q]
  · intro _
    norm_num [MonicQuadratic.coeffDist, p, q]

end ForsytheTest
