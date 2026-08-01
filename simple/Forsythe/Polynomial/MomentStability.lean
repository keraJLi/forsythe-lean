import Forsythe.Polynomial.Quadratic
import Mathlib.Tactic

/-!
# Explicit stability of the two-by-two moment system

For unit weights, a monic quadratic orthogonal to `1,z` is a rational
function of the first three moments.  This module gives a concrete Lipschitz
bound on that rational formula under a common determinant floor.  It is used
to replace informal finite-dimensional norm-equivalence and smoothness
arguments in the principal-weight perturbation analysis.
-/

set_option autoImplicit false

namespace Forsythe
namespace MomentStability

noncomputable section

/-- Determinant of the unit-mass moment matrix of `1,z`. -/
def unitMomentDet (m₁ m₂ : ℝ) : ℝ :=
  m₂ - m₁ ^ 2

/-- Cramer's-rule monic quadratic for unit mass and moments `m₁,m₂,m₃`. -/
def quadraticOfUnitMoments (m₁ m₂ m₃ : ℝ) : MonicQuadratic where
  linearCoeff := (m₁ * m₂ - m₃) / unitMomentDet m₁ m₂
  constantCoeff := (m₁ * m₃ - m₂ ^ 2) / unitMomentDet m₁ m₂

private theorem abs_mul_sub_mul_le
    {a b c d M delta : ℝ}
    (hM : 0 ≤ M) (_hdelta : 0 ≤ delta)
    (ha : |a| ≤ M) (hd : |d| ≤ M)
    (hbc : |b - d| ≤ delta) (hac : |a - c| ≤ delta) :
    |a * b - c * d| ≤ 2 * M * delta := by
  have heq : a * b - c * d = a * (b - d) + d * (a - c) := by ring
  rw [heq]
  calc
    |a * (b - d) + d * (a - c)| ≤
        |a * (b - d)| + |d * (a - c)| := abs_add_le _ _
    _ = |a| * |b - d| + |d| * |a - c| := by rw [abs_mul, abs_mul]
    _ ≤ M * delta + M * delta := by
      exact add_le_add
        (mul_le_mul ha hbc (abs_nonneg _) hM)
        (mul_le_mul hd hac (abs_nonneg _) hM)
    _ = 2 * M * delta := by ring

private theorem abs_sq_sub_sq_le
    {a b M delta : ℝ} (_hM : 0 ≤ M) (hdelta : 0 ≤ delta)
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hab : |a - b| ≤ delta) :
    |a ^ 2 - b ^ 2| ≤ 2 * M * delta := by
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul]
  have habSum : |a + b| ≤ 2 * M := by
    calc
      |a + b| ≤ |a| + |b| := abs_add_le _ _
      _ ≤ M + M := add_le_add ha hb
      _ = 2 * M := by ring
  calc
    |a - b| * |a + b| ≤ delta * (2 * M) :=
      mul_le_mul hab habSum (abs_nonneg _) hdelta
    _ = 2 * M * delta := by ring

private theorem abs_div_sub_div_le
    {u v d e U V D kappa : ℝ}
    (hkappa : 0 < kappa) (hd : kappa ≤ d) (he : kappa ≤ e)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hD : 0 ≤ D)
    (huv : |u - v| ≤ U) (hv : |v| ≤ V) (hde : |d - e| ≤ D) :
    |u / d - v / e| ≤ U / kappa + V * D / kappa ^ 2 := by
  have hdpos : 0 < d := hkappa.trans_le hd
  have hepos : 0 < e := hkappa.trans_le he
  have hidentity : u / d - v / e =
      (u - v) / d + v * (e - d) / (d * e) := by
    field_simp [ne_of_gt hdpos, ne_of_gt hepos]
    ring
  rw [hidentity]
  calc
    |(u - v) / d + v * (e - d) / (d * e)| ≤
        |(u - v) / d| + |v * (e - d) / (d * e)| := abs_add_le _ _
    _ = |u - v| / d + |v| * |d - e| / (d * e) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hdpos,
        abs_of_pos (mul_pos hdpos hepos), abs_sub_comm e d]
    _ ≤ U / kappa + V * D / kappa ^ 2 := by
      apply add_le_add
      · exact (div_le_div_iff₀ hdpos hkappa).2
          (by nlinarith [huv, hU])
      · have hnum : |v| * |d - e| ≤ V * D :=
          mul_le_mul hv hde (abs_nonneg _) hV
        have hden : kappa ^ 2 ≤ d * e := by
          nlinarith [mul_le_mul hd he hkappa.le (le_trans hkappa.le hd)]
        exact (div_le_div₀ (mul_nonneg hV hD)
          hnum (sq_pos_of_pos hkappa) hden)

/-- Concrete coefficient-distance stability for the unit-mass moment system.
The displayed constant uses only a common moment bound `M` and determinant
floor `kappa`. -/
theorem coeffDist_quadraticOfUnitMoments_le
    {m₁ m₂ m₃ n₁ n₂ n₃ M delta kappa : ℝ}
    (hM : 0 ≤ M) (hdelta : 0 ≤ delta) (hkappa : 0 < kappa)
    (hm₁ : |m₁| ≤ M) (hm₂ : |m₂| ≤ M) (_hm₃ : |m₃| ≤ M)
    (hn₁ : |n₁| ≤ M) (hn₂ : |n₂| ≤ M) (hn₃ : |n₃| ≤ M)
    (h₁ : |m₁ - n₁| ≤ delta) (h₂ : |m₂ - n₂| ≤ delta)
    (h₃ : |m₃ - n₃| ≤ delta)
    (hdetM : kappa ≤ unitMomentDet m₁ m₂)
    (hdetN : kappa ≤ unitMomentDet n₁ n₂) :
    (quadraticOfUnitMoments m₁ m₂ m₃).coeffDist
        (quadraticOfUnitMoments n₁ n₂ n₃) ≤
      ((4 * M + 2) / kappa +
        (2 * M ^ 2 + M) * (2 * M + 1) / kappa ^ 2) * delta := by
  let u₁ := m₁ * m₂ - m₃
  let v₁ := n₁ * n₂ - n₃
  let u₀ := m₁ * m₃ - m₂ ^ 2
  let v₀ := n₁ * n₃ - n₂ ^ 2
  let U := (4 * M + 2) * delta
  let V := 2 * M ^ 2 + M
  let D := (2 * M + 1) * delta
  have hU : 0 ≤ U := mul_nonneg (by linarith) hdelta
  have hV : 0 ≤ V := by nlinarith [sq_nonneg M]
  have hD : 0 ≤ D := mul_nonneg (by linarith) hdelta
  have huv₁ : |u₁ - v₁| ≤ U := by
    have hprod := abs_mul_sub_mul_le hM hdelta hm₁ hn₂ h₂ h₁
    dsimp only [u₁, v₁, U]
    calc
      |(m₁ * m₂ - m₃) - (n₁ * n₂ - n₃)| ≤
          |m₁ * m₂ - n₁ * n₂| + |m₃ - n₃| := by
        have heq : (m₁ * m₂ - m₃) - (n₁ * n₂ - n₃) =
            (m₁ * m₂ - n₁ * n₂) - (m₃ - n₃) := by ring
        rw [heq]
        exact abs_sub _ _
      _ ≤ 2 * M * delta + delta := add_le_add hprod h₃
      _ ≤ (4 * M + 2) * delta := by nlinarith
  have huv₀ : |u₀ - v₀| ≤ U := by
    have hprod := abs_mul_sub_mul_le hM hdelta hm₁ hn₃ h₃ h₁
    have hsq := abs_sq_sub_sq_le hM hdelta hm₂ hn₂ h₂
    dsimp only [u₀, v₀, U]
    calc
      |(m₁ * m₃ - m₂ ^ 2) - (n₁ * n₃ - n₂ ^ 2)| ≤
          |m₁ * m₃ - n₁ * n₃| + |m₂ ^ 2 - n₂ ^ 2| := by
        have heq : (m₁ * m₃ - m₂ ^ 2) - (n₁ * n₃ - n₂ ^ 2) =
            (m₁ * m₃ - n₁ * n₃) - (m₂ ^ 2 - n₂ ^ 2) := by ring
        rw [heq]
        exact abs_sub _ _
      _ ≤ 2 * M * delta + 2 * M * delta := add_le_add hprod hsq
      _ ≤ (4 * M + 2) * delta := by nlinarith
  have hv₁ : |v₁| ≤ V := by
    dsimp only [v₁, V]
    calc
      |n₁ * n₂ - n₃| ≤ |n₁ * n₂| + |n₃| := abs_sub _ _
      _ = |n₁| * |n₂| + |n₃| := by rw [abs_mul]
      _ ≤ M * M + M := add_le_add (mul_le_mul hn₁ hn₂ (abs_nonneg _) hM) hn₃
      _ ≤ 2 * M ^ 2 + M := by nlinarith [sq_nonneg M]
  have hv₀ : |v₀| ≤ V := by
    dsimp only [v₀, V]
    calc
      |n₁ * n₃ - n₂ ^ 2| ≤ |n₁ * n₃| + |n₂ ^ 2| := abs_sub _ _
      _ = |n₁| * |n₃| + |n₂| ^ 2 := by rw [abs_mul, abs_pow]
      _ ≤ M * M + M ^ 2 := by
        exact add_le_add (mul_le_mul hn₁ hn₃ (abs_nonneg _) hM)
          (pow_le_pow_left₀ (abs_nonneg n₂) hn₂ 2)
      _ ≤ 2 * M ^ 2 + M := by nlinarith
  have hdetDiff :
      |unitMomentDet m₁ m₂ - unitMomentDet n₁ n₂| ≤ D := by
    have hsq := abs_sq_sub_sq_le hM hdelta hm₁ hn₁ h₁
    dsimp only [unitMomentDet, D]
    calc
      |(m₂ - m₁ ^ 2) - (n₂ - n₁ ^ 2)| ≤
          |m₂ - n₂| + |m₁ ^ 2 - n₁ ^ 2| := by
        have heq : (m₂ - m₁ ^ 2) - (n₂ - n₁ ^ 2) =
            (m₂ - n₂) - (m₁ ^ 2 - n₁ ^ 2) := by ring
        rw [heq]
        exact abs_sub _ _
      _ ≤ delta + 2 * M * delta := add_le_add h₂ hsq
      _ = (2 * M + 1) * delta := by ring
  have hlinear := abs_div_sub_div_le hkappa hdetM hdetN hU hV hD
    huv₁ hv₁ hdetDiff
  have hconstant := abs_div_sub_div_le hkappa hdetM hdetN hU hV hD
    huv₀ hv₀ hdetDiff
  rw [MonicQuadratic.coeffDist]
  change max
      |u₁ / unitMomentDet m₁ m₂ - v₁ / unitMomentDet n₁ n₂|
      |u₀ / unitMomentDet m₁ m₂ - v₀ / unitMomentDet n₁ n₂| ≤ _
  apply max_le
  · calc
      |u₁ / unitMomentDet m₁ m₂ - v₁ / unitMomentDet n₁ n₂| ≤
          U / kappa + V * D / kappa ^ 2 := hlinear
      _ = ((4 * M + 2) / kappa +
          (2 * M ^ 2 + M) * (2 * M + 1) / kappa ^ 2) * delta := by
        dsimp only [U, V, D]
        field_simp [ne_of_gt hkappa]
  · calc
      |u₀ / unitMomentDet m₁ m₂ - v₀ / unitMomentDet n₁ n₂| ≤
          U / kappa + V * D / kappa ^ 2 := hconstant
      _ = ((4 * M + 2) / kappa +
          (2 * M ^ 2 + M) * (2 * M + 1) / kappa ^ 2) * delta := by
        dsimp only [U, V, D]
        field_simp [ne_of_gt hkappa]

end

end MomentStability
end Forsythe
