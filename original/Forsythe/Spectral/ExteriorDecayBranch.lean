import Forsythe.Exterior.Decay
import Forsythe.Spectral.FourNodeBranch
import Forsythe.Spectral.Stabilization

/-!
# Geometric exterior decay in the four-node spectral branch

This file joins the finite-dimensional spectral reduction to the scalar
exterior-decay machinery.  The exterior index type contains precisely the
surviving grouped eigenspaces which are not one of the four principal nodes.
Thus components deleted before stabilization never enter the logarithmic
cocycle, where strict positivity is essential.
-/

set_option autoImplicit false

namespace Forsythe
namespace Spectral

open Filter Module.End Polynomial Set Topology
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The finite set of surviving eigenvalues outside the four principal
nodes, bundled as a type so that finite sums can use `Fintype`. -/
abbrev StableExteriorIndex
    (A : Module.End ℝ E) (S : Finset A.Eigenvalues)
    (nodes : Fin 4 → A.Eigenvalues) :=
  {mu : A.Eigenvalues // mu ∈ S ∧ mu ∉ Set.range nodes}

instance stableExteriorIndexFintype
    (A : Module.End ℝ E) (S : Finset A.Eigenvalues)
    (nodes : Fin 4 → A.Eigenvalues) :
    Fintype (StableExteriorIndex A S nodes) :=
  Fintype.ofFinite _

omit [FiniteDimensional ℝ E] in
@[simp]
theorem stableExteriorIndex_mem_stable
    (A : Module.End ℝ E) (S : Finset A.Eigenvalues)
    (nodes : Fin 4 → A.Eigenvalues)
    (mu : StableExteriorIndex A S nodes) : (mu : A.Eigenvalues) ∈ S :=
  mu.property.1

omit [FiniteDimensional ℝ E] in
theorem stableExteriorIndex_not_mem_nodes
    (A : Module.End ℝ E) (S : Finset A.Eigenvalues)
    (nodes : Fin 4 → A.Eigenvalues)
    (mu : StableExteriorIndex A S nodes) :
    (mu : A.Eigenvalues) ∉ Set.range nodes :=
  mu.property.2

/-- A positive weight which tends to zero cannot have a limiting two-step
multiplier of absolute value greater than one.  This is the scalar argument
which turns qualitative exterior decay into `|Q(mu)| ≤ H`. -/
theorem abs_limitNumerator_le_of_positive_weight_tendsto_zero
    (weight numerator denominator : ℕ → ℝ) (a H : ℝ)
    (hweightPos : ∀ᶠ k in atTop, 0 < weight (2 * k))
    (hrec : ∀ k, weight (k + 2) =
      (numerator k / denominator k) ^ 2 * weight k)
    (hweightZero : Tendsto (fun k ↦ weight (2 * k)) atTop (nhds 0))
    (hnumerator : Tendsto numerator atTop (nhds a))
    (hdenominator : Tendsto denominator atTop (nhds H))
    (hH : 0 < H) :
    |a| ≤ H := by
  by_contra hnot
  have ha : H < |a| := lt_of_not_ge hnot
  have hquot : Tendsto (fun k ↦ numerator k / denominator k) atTop
      (nhds (a / H)) :=
    hnumerator.div hdenominator (ne_of_gt hH)
  have hsq : Tendsto (fun k ↦ (numerator k / denominator k) ^ 2) atTop
      (nhds ((a / H) ^ 2)) := hquot.pow 2
  have hlimitSq : 1 < (a / H) ^ 2 := by
    have habsDiv : 1 < |a / H| := by
      rw [abs_div, abs_of_pos hH]
      exact (one_lt_div hH).2 ha
    nlinarith [abs_nonneg (a / H), sq_abs (a / H)]
  have htwo : Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    exact eventually_atTop.2 ⟨N, fun k hk ↦ by omega⟩
  have hmult : ∀ᶠ k in atTop,
      1 < (numerator (2 * k) / denominator (2 * k)) ^ 2 := by
    have hraw : ∀ᶠ k in atTop,
        1 < (numerator k / denominator k) ^ 2 :=
      (tendsto_order.1 hsq).1 1 hlimitSq
    exact htwo.eventually hraw
  have hinc : ∀ᶠ k in atTop, weight (2 * k) < weight (2 * (k + 1)) := by
    filter_upwards [hweightPos, hmult] with k hw hm
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, hrec]
    nlinarith
  obtain ⟨Kinc, hKinc⟩ := eventually_atTop.1 hinc
  obtain ⟨Kpos, hKpos⟩ := eventually_atTop.1 hweightPos
  let L := max Kinc Kpos
  have hLpos : 0 < weight (2 * L) :=
    hKpos L (le_max_right Kinc Kpos)
  have hstep : ∀ k, L ≤ k → weight (2 * k) < weight (2 * (k + 1)) := by
    intro k hk
    exact hKinc k ((le_max_left Kinc Kpos).trans hk)
  have hlowerAll : ∀ k, L ≤ k → weight (2 * L) ≤ weight (2 * k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact ih.trans (hstep k hk).le
  have hlower : ∀ᶠ k in atTop, weight (2 * L) ≤ weight (2 * k) := by
    refine eventually_atTop.2 ⟨L, ?_⟩
    intro k hk
    exact hlowerAll k hk
  have hsmall : ∀ᶠ k in atTop, weight (2 * k) < weight (2 * L) := by
    have := (tendsto_order.1 hweightZero).2 (weight (2 * L)) hLpos
    exact this
  obtain ⟨k, hkLower, hkSmall⟩ := (hlower.and hsmall).exists
  exact (not_lt_of_ge hkLower) hkSmall

/-- In the stabilized four-node branch every surviving exterior spectral
value lies in the closed multiplier interval `[-tau²,tau²]`.  The proof uses
the exact component recurrence and the already established qualitative
vanishing of each exterior weight. -/
theorem fourNode_exterior_product_abs_le_tau_sq
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (htau : 0 < tau) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (hproduct : Tendsto (fun k ↦ Arnoldi.quadraticProductCoeff
      (arnoldiFactorOrbit2 A v₀ k)
      (arnoldiFactorOrbit2 A v₀ (k + 1))) atTop
      (nhds (Arnoldi.quadraticProductCoeff p q)))
    (nodes : Fin 4 → A.Eigenvalues)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    {K : ℕ} {S : Finset A.Eigenvalues}
    (hstable : ∀ l, K ≤ l →
      active A hA (arnoldiOrbit2 A v₀ l) = S)
    (mu : A.Eigenvalues) (hmuS : mu ∈ S)
    (hmuOutside : mu ∉ Set.range nodes) :
    |(p.toPolynomial * q.toPolynomial).eval (mu : ℝ)| ≤ tau ^ 2 := by
  let w : ℕ → ℝ := fun k ↦
    weight A hA (arnoldiOrbit2 A v₀ k) mu
  let num : ℕ → ℝ := fun k ↦
    ((arnoldiFactorOrbit2 A v₀ k).toPolynomial *
      (arnoldiFactorOrbit2 A v₀ (k + 1)).toPolynomial).eval (mu : ℝ)
  let den : ℕ → ℝ := fun k ↦
    arnoldiNormalizerOrbit2 A v₀ k *
      arnoldiNormalizerOrbit2 A v₀ (k + 1)
  have hwpos : ∀ᶠ k in atTop, 0 < w (2 * k) := by
    refine eventually_atTop.2 ⟨K, ?_⟩
    intro k hk
    have hcomponent : component A hA
        (arnoldiOrbit2 A v₀ (2 * k)) mu ≠ 0 :=
      component_ne_zero_of_mem_stable_active A hA v₀ hstable hmuS
        (by omega)
    dsimp only [w, weight]
    exact sq_pos_of_pos (norm_pos_iff.mpr hcomponent)
  have hwrec : ∀ k, w (k + 2) = (num k / den k) ^ 2 * w k := by
    intro k
    exact weight_arnoldiOrbit2_add_two A hA v₀ mu k
  have hwzero : Tendsto (fun k ↦ w (2 * k)) atTop (nhds 0) := by
    simpa only [w] using even_exterior_weight_tendsto_zero
      A hA v₀ hv₀ hgrade₀ tau p q hp hq hnormalizer nodes hfactor
        mu hmuOutside
  have hnum : Tendsto num atTop
      (nhds ((p.toPolynomial * q.toPolynomial).eval (mu : ℝ))) := by
    have ht := Exterior.tendsto_quadraticProduct_eval_of_tendsto_coeff
      (P := arnoldiFactorOrbit2 A v₀)
      (Q := fun k ↦ arnoldiFactorOrbit2 A v₀ (k + 1))
      (p := p) (q := q) (mu : ℝ) hproduct
    simpa only [num, Polynomial.eval_mul] using ht
  have hnormalizerShift : Tendsto
      (fun k ↦ arnoldiNormalizerOrbit2 A v₀ (k + 1)) atTop (nhds tau) :=
    hnormalizer.comp (tendsto_add_atTop_nat 1)
  have hden : Tendsto den atTop (nhds (tau ^ 2)) := by
    simpa only [den, pow_two] using hnormalizer.mul hnormalizerShift
  exact abs_limitNumerator_le_of_positive_weight_tendsto_zero
    w num den ((p.toPolynomial * q.toPolynomial).eval (mu : ℝ))
      (tau ^ 2) hwpos hwrec hwzero hnum hden (sq_pos_of_pos htau)

/- The positive neutral value is impossible away from the four nodes: after
subtracting `tau²`, the limiting product is the nodal quartic. -/
omit [FiniteDimensional ℝ E] in
theorem fourNode_exterior_product_ne_tau_sq
    (A : Module.End ℝ E) (nodes : Fin 4 → A.Eigenvalues)
    (p q : MonicQuadratic) (tau : ℝ)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    (mu : A.Eigenvalues) (hmuOutside : mu ∉ Set.range nodes) :
    (p.toPolynomial * q.toPolynomial).eval (mu : ℝ) ≠ tau ^ 2 := by
  intro hneutral
  have heval := congrArg (Polynomial.eval (mu : ℝ)) hfactor
  have hPiZero :
      (FourNode.nodalQuartic
        (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ))).eval (mu : ℝ) = 0 := by
    simp only [eval_add, eval_C] at heval
    linarith
  rw [FourNode.nodalQuartic, eval_prod, Finset.prod_eq_zero_iff] at hPiZero
  simp only [Finset.mem_univ, eval_sub, eval_X, eval_C, true_and] at hPiZero
  obtain ⟨i, hi⟩ := hPiZero
  apply hmuOutside
  refine ⟨i, Subtype.ext ?_⟩
  exact (sub_eq_zero.mp hi).symm

/- At each principal node the nodal quartic vanishes, so the limiting
two-step product has value `tau²`. -/
omit [FiniteDimensional ℝ E] in
theorem fourNode_product_eval_node_eq_tau_sq
    (A : Module.End ℝ E) (nodes : Fin 4 → A.Eigenvalues)
    (p q : MonicQuadratic) (tau : ℝ)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    (i : Fin 4) :
    (p.toPolynomial * q.toPolynomial).eval (nodes i : ℝ) = tau ^ 2 := by
  have hPi : (FourNode.nodalQuartic
      (fun j ↦ ((nodes j : A.Eigenvalues) : ℝ))).eval (nodes i : ℝ) = 0 := by
    rw [FourNode.nodalQuartic, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have heval := congrArg (Polynomial.eval (nodes i : ℝ)) hfactor
  simpa only [eval_add, eval_C, hPi, zero_add] using heval

/-- No factor product can vanish on a surviving component after
stabilization, because the exact two-step recurrence would delete it. -/
theorem twoStepProduct_eval_ne_zero_of_mem_stable
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    {K : ℕ} {S : Finset A.Eigenvalues}
    (hstable : ∀ n, K ≤ n → active A hA (arnoldiOrbit2 A v₀ n) = S)
    (mu : A.Eigenvalues) (hmuS : mu ∈ S)
    (l : ℕ) (hl : K ≤ l) :
    ((arnoldiFactorOrbit2 A v₀ l).toPolynomial *
      (arnoldiFactorOrbit2 A v₀ (l + 1)).toPolynomial).eval (mu : ℝ) ≠ 0 := by
  intro hzero
  have hrec := component_arnoldiOrbit2_add_two A hA v₀ mu l
  rw [hzero, zero_div, zero_smul] at hrec
  exact component_ne_zero_of_mem_stable_active A hA v₀ hstable hmuS
    (show K ≤ l + 2 by omega) hrec

/-- The evaluation norm of the four free coefficients of a monic quartic.
The leading coefficients cancel when two quadratic products are subtracted. -/
def quarticFreeEvalScale (t : ℝ) : ℝ :=
  |t| ^ 3 + |t| ^ 2 + |t| + 1

omit [FiniteDimensional ℝ E] in
theorem quarticFreeEvalScale_nonneg (t : ℝ) :
    0 ≤ quarticFreeEvalScale t := by
  dsimp only [quarticFreeEvalScale]
  positivity

/- Concrete max-norm control of a product evaluation.  This is the bridge
from the coefficient-tail estimate to the explicit logarithmic error bound. -/
omit [FiniteDimensional ℝ E] in
theorem abs_quadraticProduct_eval_sub_le
    (p q r s : MonicQuadratic) (t : ℝ) :
    |(p.toPolynomial * q.toPolynomial).eval t -
        (r.toPolynomial * s.toPolynomial).eval t| ≤
      quarticFreeEvalScale t *
        dist (Arnoldi.quadraticProductCoeff p q)
          (Arnoldi.quadraticProductCoeff r s) := by
  let c := Arnoldi.quadraticProductCoeff p q
  let d := Arnoldi.quadraticProductCoeff r s
  let D := dist c d
  have hc3 : |c.1.1 - d.1.1| ≤ D := by
    dsimp only [D]
    rw [dist_eq_norm]
    change |c.1.1 - d.1.1| ≤
      max (max |c.1.1 - d.1.1| |c.1.2 - d.1.2|)
        (max |c.2.1 - d.2.1| |c.2.2 - d.2.2|)
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hc2 : |c.1.2 - d.1.2| ≤ D := by
    dsimp only [D]
    rw [dist_eq_norm]
    change |c.1.2 - d.1.2| ≤
      max (max |c.1.1 - d.1.1| |c.1.2 - d.1.2|)
        (max |c.2.1 - d.2.1| |c.2.2 - d.2.2|)
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hc1 : |c.2.1 - d.2.1| ≤ D := by
    dsimp only [D]
    rw [dist_eq_norm]
    change |c.2.1 - d.2.1| ≤
      max (max |c.1.1 - d.1.1| |c.1.2 - d.1.2|)
        (max |c.2.1 - d.2.1| |c.2.2 - d.2.2|)
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hc0 : |c.2.2 - d.2.2| ≤ D := by
    dsimp only [D]
    rw [dist_eq_norm]
    change |c.2.2 - d.2.2| ≤
      max (max |c.1.1 - d.1.1| |c.1.2 - d.1.2|)
        (max |c.2.1 - d.2.1| |c.2.2 - d.2.2|)
    exact (le_max_right _ _).trans (le_max_right _ _)
  have heval :
      (p.toPolynomial * q.toPolynomial).eval t -
          (r.toPolynomial * s.toPolynomial).eval t =
        (c.1.1 - d.1.1) * t ^ 3 +
          (c.1.2 - d.1.2) * t ^ 2 +
          (c.2.1 - d.2.1) * t + (c.2.2 - d.2.2) := by
    dsimp only [c, d, Arnoldi.quadraticProductCoeff]
    simp only [eval_mul, MonicQuadratic.eval]
    ring
  rw [heval]
  calc
    |(c.1.1 - d.1.1) * t ^ 3 +
        (c.1.2 - d.1.2) * t ^ 2 +
        (c.2.1 - d.2.1) * t + (c.2.2 - d.2.2)| ≤
      |c.1.1 - d.1.1| * |t ^ 3| +
        |c.1.2 - d.1.2| * |t ^ 2| +
        |c.2.1 - d.2.1| * |t| + |c.2.2 - d.2.2| := by
      calc
        |(c.1.1 - d.1.1) * t ^ 3 +
            (c.1.2 - d.1.2) * t ^ 2 +
            (c.2.1 - d.2.1) * t + (c.2.2 - d.2.2)| ≤
          |(c.1.1 - d.1.1) * t ^ 3| +
            |(c.1.2 - d.1.2) * t ^ 2| +
            |(c.2.1 - d.2.1) * t| + |c.2.2 - d.2.2| := by
              linarith [abs_add_le
                ((c.1.1 - d.1.1) * t ^ 3 +
                  (c.1.2 - d.1.2) * t ^ 2 +
                  (c.2.1 - d.2.1) * t)
                (c.2.2 - d.2.2),
                abs_add_le
                  ((c.1.1 - d.1.1) * t ^ 3 +
                    (c.1.2 - d.1.2) * t ^ 2)
                  ((c.2.1 - d.2.1) * t),
                abs_add_le ((c.1.1 - d.1.1) * t ^ 3)
                  ((c.1.2 - d.1.2) * t ^ 2)]
        _ = _ := by simp only [abs_mul]
    _ ≤ D * |t ^ 3| + D * |t ^ 2| + D * |t| + D := by
      gcongr
    _ = quarticFreeEvalScale t * D := by
      simp only [abs_pow]
      dsimp only [quarticFreeEvalScale]
      ring

/-- Exact normalization identity behind the negative-neutral cocycle.  The
Lagrange coefficients sum to one, so the common denominator occurs twice;
its logarithm is exactly the pair of height-defect logarithms. -/
theorem normalized_lagrange_log_identity
    {lambda : Fin 4 → ℝ} (hlambda : Function.Injective lambda)
    (f : Polynomial ℝ) (t H sigma sigma' : ℝ)
    (hH : 0 < H) (hsigma : 0 < sigma) (hsigma' : 0 < sigma')
    (hext : 0 < 1 - f.eval t / H)
    (hnodes : ∀ i, 0 < 1 + f.eval (lambda i) / H) :
    2 * Real.log ((H - f.eval t) / (sigma * sigma')) +
        ∑ i : Fin 4, Exterior.lagrangeWeight lambda t i *
          (2 * Real.log ((H + f.eval (lambda i)) / (sigma * sigma'))) =
      2 * (Real.log (1 - f.eval t / H) +
          ∑ i : Fin 4, Exterior.lagrangeWeight lambda t i *
            Real.log (1 + f.eval (lambda i) / H) -
        Real.log (1 - (H - sigma ^ 2) / H) -
        Real.log (1 - (H - sigma' ^ 2) / H)) := by
  have hHne : H ≠ 0 := ne_of_gt hH
  have hsigmaNe : sigma ≠ 0 := ne_of_gt hsigma
  have hsigma'Ne : sigma' ≠ 0 := ne_of_gt hsigma'
  have hlogExt :
      Real.log ((H - f.eval t) / (sigma * sigma')) =
        Real.log (1 - f.eval t / H) + Real.log H -
          Real.log sigma - Real.log sigma' := by
    have heq : H - f.eval t = (1 - f.eval t / H) * H := by
      field_simp
    rw [heq, Real.log_div (mul_ne_zero (ne_of_gt hext) hHne)
      (mul_ne_zero hsigmaNe hsigma'Ne),
      Real.log_mul (ne_of_gt hext) hHne,
      Real.log_mul hsigmaNe hsigma'Ne]
    ring
  have hlogNode (i : Fin 4) :
      Real.log ((H + f.eval (lambda i)) / (sigma * sigma')) =
        Real.log (1 + f.eval (lambda i) / H) + Real.log H -
          Real.log sigma - Real.log sigma' := by
    have heq : H + f.eval (lambda i) =
        (1 + f.eval (lambda i) / H) * H := by
      field_simp
    rw [heq, Real.log_div (mul_ne_zero (ne_of_gt (hnodes i)) hHne)
      (mul_ne_zero hsigmaNe hsigma'Ne),
      Real.log_mul (ne_of_gt (hnodes i)) hHne,
      Real.log_mul hsigmaNe hsigma'Ne]
    ring
  have hlogDefect :
      Real.log (1 - (H - sigma ^ 2) / H) =
        2 * Real.log sigma - Real.log H := by
    have heq : 1 - (H - sigma ^ 2) / H = sigma ^ 2 / H := by
      field_simp
      ring
    rw [heq, Real.log_div (pow_ne_zero 2 hsigmaNe) hHne,
      Real.log_pow]
    norm_num
  have hlogDefect' :
      Real.log (1 - (H - sigma' ^ 2) / H) =
        2 * Real.log sigma' - Real.log H := by
    have heq : 1 - (H - sigma' ^ 2) / H = sigma' ^ 2 / H := by
      field_simp
      ring
    rw [heq, Real.log_div (pow_ne_zero 2 hsigma'Ne) hHne,
      Real.log_pow]
    norm_num
  rw [hlogExt, hlogDefect, hlogDefect']
  simp_rw [hlogNode]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [Exterior.sum_lagrangeWeight hlambda t]
  ring_nf
  rw [← Finset.sum_mul]

omit [FiniteDimensional ℝ E] in
theorem quadraticProduct_sub_natDegree_le_three
    (p q r s : MonicQuadratic) :
    (p.toPolynomial * q.toPolynomial -
      r.toPolynomial * s.toPolynomial).natDegree ≤ 3 := by
  have hpq : (p.toPolynomial * q.toPolynomial).IsMonicOfDegree 4 := by
    refine ⟨?_, (MonicQuadratic.monic p).mul (MonicQuadratic.monic q)⟩
    rw [(MonicQuadratic.monic p).natDegree_mul (MonicQuadratic.monic q),
      natDegree_monicQuadratic, natDegree_monicQuadratic]
  have hrs : (r.toPolynomial * s.toPolynomial).IsMonicOfDegree 4 := by
    refine ⟨?_, (MonicQuadratic.monic r).mul (MonicQuadratic.monic s)⟩
    rw [(MonicQuadratic.monic r).natDegree_mul (MonicQuadratic.monic s),
      natDegree_monicQuadratic, natDegree_monicQuadratic]
  have hlt := hpq.natDegree_sub_lt (by norm_num : (4 : ℕ) ≠ 0) hrs
  omega

/-- The coefficient-tail estimate gives the explicit quadratic logarithmic
error required by the negative-neutral cocycle. -/
theorem eventually_signed_logError_le_sq_of_productCoeff_tail
    (P : ℕ → MonicQuadratic) (p q : MonicQuadratic)
    (lambda : Fin 4 → ℝ) (hlambda : Function.Injective lambda)
    (t H C : ℝ) (defect : ℕ → ℝ)
    (hH : 0 < H) (hC : 0 ≤ C)
    (hdefect : ∀ k, 0 ≤ defect k)
    (hdefectZero : Tendsto defect atTop (nhds 0))
    (htail : ∀ k,
      dist (Arnoldi.quadraticProductCoeff (P k) (P (k + 1)))
        (Arnoldi.quadraticProductCoeff p q) ≤ C * defect k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      |Real.log (1 -
          ((P k).toPolynomial * (P (k + 1)).toPolynomial -
            p.toPolynomial * q.toPolynomial).eval t / H) +
        ∑ i : Fin 4, Exterior.lagrangeWeight lambda t i *
          Real.log (1 +
            ((P k).toPolynomial * (P (k + 1)).toPolynomial -
              p.toPolynomial * q.toPolynomial).eval (lambda i) / H)| ≤
        B * (defect k) ^ 2 := by
  let R := quarticFreeEvalScale t +
    ∑ i : Fin 4, quarticFreeEvalScale (lambda i)
  let D := R * C / H
  let B := 2 * D ^ 2 *
    (1 + ∑ i : Fin 4, |Exterior.lagrangeWeight lambda t i|)
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg (quarticFreeEvalScale_nonneg t)
      (Finset.sum_nonneg fun i hi ↦ quarticFreeEvalScale_nonneg (lambda i))
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hR hC) hH.le
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hscaleT : quarticFreeEvalScale t ≤ R := by
    dsimp only [R]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun i hi ↦ quarticFreeEvalScale_nonneg (lambda i))
  have hscaleNode (i : Fin 4) : quarticFreeEvalScale (lambda i) ≤ R := by
    have hle : quarticFreeEvalScale (lambda i) ≤
        ∑ j : Fin 4, quarticFreeEvalScale (lambda j) :=
      Finset.single_le_sum
        (fun j hj ↦ quarticFreeEvalScale_nonneg (lambda j))
        (Finset.mem_univ i)
    exact hle.trans (le_add_of_nonneg_left (quarticFreeEvalScale_nonneg t))
  have heval (k : ℕ) (x : ℝ) :
      |((P k).toPolynomial * (P (k + 1)).toPolynomial -
          p.toPolynomial * q.toPolynomial).eval x| ≤
        quarticFreeEvalScale x *
          dist (Arnoldi.quadraticProductCoeff (P k) (P (k + 1)))
            (Arnoldi.quadraticProductCoeff p q) := by
    simpa only [eval_sub] using
      abs_quadraticProduct_eval_sub_le (P k) (P (k + 1)) p q x
  have hratio (k : ℕ) (x : ℝ) (hx : quarticFreeEvalScale x ≤ R) :
      |((P k).toPolynomial * (P (k + 1)).toPolynomial -
          p.toPolynomial * q.toPolynomial).eval x / H| ≤
        D * defect k := by
    rw [abs_div, abs_of_pos hH]
    calc
      |((P k).toPolynomial * (P (k + 1)).toPolynomial -
          p.toPolynomial * q.toPolynomial).eval x| / H ≤
        (quarticFreeEvalScale x *
          dist (Arnoldi.quadraticProductCoeff (P k) (P (k + 1)))
            (Arnoldi.quadraticProductCoeff p q)) / H := by
              exact div_le_div_of_nonneg_right (heval k x) hH.le
      _ ≤ (quarticFreeEvalScale x * (C * defect k)) / H := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (htail k)
            (quarticFreeEvalScale_nonneg x)) hH.le
      _ ≤ (R * (C * defect k)) / H := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hx (mul_nonneg hC (hdefect k))) hH.le
      _ = D * defect k := by
        dsimp only [D]
        ring
  have hsmall : ∀ᶠ k in atTop, D * defect k ≤ (1 : ℝ) / 2 := by
    have ht : Tendsto (fun k ↦ D * defect k) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hdefectZero
    exact ((tendsto_order.1 ht).2 ((1 : ℝ) / 2) (by norm_num)).mono
      fun k hk ↦ hk.le
  refine ⟨B, hB, ?_⟩
  filter_upwards [hsmall] with k hk
  let f := (P k).toPolynomial * (P (k + 1)).toPolynomial -
    p.toPolynomial * q.toPolynomial
  have hf : f.natDegree ≤ 3 := by
    exact quadraticProduct_sub_natDegree_le_three (P k) (P (k + 1)) p q
  have hbound := Exterior.abs_signed_lagrange_log_firstVariation_le_mul_sq
    hlambda f hf t H D (defect k) hD (hdefect k)
      (by simpa only [f] using hratio k t hscaleT)
      (fun i ↦ by simpa only [f] using hratio k (lambda i) (hscaleNode i)) hk
  simpa only [f, B] using hbound

/-- A surviving exterior component forces the limiting height to remain
strictly above every tail height.  Equality would make the deterministic
orbit exactly two-periodic, contradicting qualitative exterior decay. -/
theorem arnoldiHeightOrbit2_lt_tau_sq_of_mem_stable_exterior
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (p q : MonicQuadratic)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (nodes : Fin 4 → A.Eigenvalues)
    (hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2))
    {K : ℕ} {S : Finset A.Eigenvalues}
    (hstable : ∀ n, K ≤ n → active A hA (arnoldiOrbit2 A v₀ n) = S)
    (mu : A.Eigenvalues) (hmuS : mu ∈ S)
    (hmuOutside : mu ∉ Set.range nodes)
    (l : ℕ) (hl : K ≤ l) :
    Arnoldi.arnoldiHeightOrbit2 A v₀ l < tau ^ 2 := by
  let H : ℕ → ℝ := Arnoldi.arnoldiHeightOrbit2 A v₀
  have hHlimit : Tendsto H atTop (nhds (tau ^ 2)) := by
    change Tendsto (fun k ↦ arnoldiNormalizerOrbit2 A v₀ k ^ 2)
      atTop (nhds (tau ^ 2))
    exact hnormalizer.pow 2
  have hmono : Monotone H := by
    change Monotone (quadraticStepHeight (arnoldiNormalizerOrbit2 A v₀))
    exact arnoldiOrbit2_height_monotone A hA v₀ hv₀ hgrade₀
  have hle : H l ≤ tau ^ 2 := hmono.ge_of_tendsto hHlimit l
  apply lt_of_le_of_ne hle
  intro heq
  have hnextLe : H (l + 1) ≤ tau ^ 2 := hmono.ge_of_tendsto hHlimit (l + 1)
  have hnextGe : H l ≤ H (l + 1) := hmono (Nat.le_add_right l 1)
  have hheightEq : H (l + 1) = H l := by linarith
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  have henergy : quadraticStepEnergy A (arnoldiOrbit2 A v₀)
      (arnoldiFactorOrbit2 A v₀) (arnoldiNormalizerOrbit2 A v₀) l = 0 :=
    (hsteps.energy_eq_zero_iff_height_eq hA l).2 (by
      simpa only [H, Arnoldi.arnoldiHeightOrbit2] using hheightEq)
  have hperiodic := arnoldiOrbit2_eventually_two_periodic_of_energy_eq_zero
    A hA v₀ hv₀ hgrade₀ henergy
  have horbit (r : ℕ) : arnoldiOrbit2 A v₀ (2 * l + 2 * r) =
      arnoldiOrbit2 A v₀ (2 * l) := by
    induction r with
    | zero => simp
    | succ r ihr =>
        have hstep := hperiodic (2 * l + 2 * r) (by omega)
        rw [show 2 * l + 2 * (r + 1) = (2 * l + 2 * r) + 2 by omega,
          hstep, ihr]
  let w : ℕ → ℝ := fun k ↦
    weight A hA (arnoldiOrbit2 A v₀ (2 * k)) mu
  have hwzero : Tendsto w atTop (nhds 0) := by
    simpa only [w] using even_exterior_weight_tendsto_zero
      A hA v₀ hv₀ hgrade₀ tau p q hp hq hnormalizer nodes hfactor
        mu hmuOutside
  have hwshift : Tendsto (fun r ↦ w (l + r)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      hwzero.comp (tendsto_add_atTop_nat l)
  have hwconst : (fun r ↦ w (l + r)) = fun _r ↦ w l := by
    funext r
    dsimp only [w]
    rw [show 2 * (l + r) = 2 * l + 2 * r by omega, horbit]
  rw [hwconst] at hwshift
  have hwEq : w l = 0 := tendsto_nhds_unique tendsto_const_nhds hwshift
  have hcomponent : component A hA
      (arnoldiOrbit2 A v₀ (2 * l)) mu ≠ 0 :=
    component_ne_zero_of_mem_stable_active A hA v₀ hstable hmuS (by omega)
  have hwpos : 0 < w l := by
    dsimp only [w, weight]
    exact sq_pos_of_pos (norm_pos_iff.mpr hcomponent)
  rw [hwEq] at hwpos
  exact (lt_irrefl 0) hwpos

/- Removing a finite even prefix from an even cluster subsequence preserves
cofinality and convergence. -/
omit [FiniteDimensional ℝ E] in
theorem exists_shifted_subsequence_of_mem_evenClusterSet
    (A : Module.End ℝ E) (v₀ vStar : E)
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k))) (m : ℕ) :
    ∃ phi : ℕ → ℕ, Tendsto phi atTop atTop ∧
      Tendsto (fun j ↦ arnoldiOrbit2 A v₀ (2 * m + 2 * phi j))
        atTop (nhds vStar) := by
  obtain ⟨psi, hpsiMono, hpsiLimit⟩ :=
    (show MapClusterPt vStar atTop
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)) from hvStar).tendsto_subseq
  let phi : ℕ → ℕ := fun j ↦ psi (j + m) - m
  have hpsi : Tendsto psi atTop atTop := hpsiMono.tendsto_atTop
  have hshift : Tendsto (fun j ↦ psi (j + m)) atTop atTop :=
    hpsi.comp (tendsto_add_atTop_nat m)
  have hphi : Tendsto phi atTop atTop := by
    exact (tendsto_sub_atTop_nat m).comp hshift
  refine ⟨phi, hphi, ?_⟩
  have hlimit : Tendsto
      (fun j ↦ arnoldiOrbit2 A v₀ (2 * psi (j + m)))
      atTop (nhds vStar) := by
    simpa only [Function.comp_def] using
      hpsiLimit.comp (tendsto_add_atTop_nat m)
  convert hlimit using 1
  funext j
  congr 2
  dsimp only [phi]
  have hm : m ≤ psi (j + m) :=
    (Nat.le_add_left m j).trans (hpsiMono.id_le (j + m))
  omega

/-- A surviving exterior node cannot have limiting product `-tau²`.  This is
the operator-level instantiation of the Lagrange/logarithmic cocycle: the
coefficient tail makes the full first variation quadratically small, while a
grade-four even cluster point forces the cocycle to minus infinity. -/
theorem fourNode_stableExterior_product_ne_neg_tau_sq
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (htau : 0 < tau) (p q : MonicQuadratic)
    (Kprod : ℕ) (Ctail : ℝ) (hCtail : 0 ≤ Ctail)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (hproduct : Tendsto (fun k ↦ Arnoldi.quadraticProductCoeff
      (arnoldiFactorOrbit2 A v₀ k)
      (arnoldiFactorOrbit2 A v₀ (k + 1))) atTop
      (nhds (Arnoldi.quadraticProductCoeff p q)))
    (htail : ∀ n, dist
      (Arnoldi.quadraticProductCoeff
        (arnoldiFactorOrbit2 A v₀ (n + Kprod))
        (arnoldiFactorOrbit2 A v₀ (n + Kprod + 1)))
      (Arnoldi.quadraticProductCoeff p q) ≤
        Ctail * (tau ^ 2 -
          Arnoldi.arnoldiHeightOrbit2 A v₀ (n + Kprod)))
    (Kstable : ℕ) (S : Finset A.Eigenvalues)
    (hstable : ∀ n, Kstable ≤ n →
      active A hA (arnoldiOrbit2 A v₀ n) = S)
    (vStar : E)
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)))
    (hcard : (active A hA vStar).card = 4)
    (hnodesStable : ∀ i,
      nodesOfFourClusterPoint A hA vStar hcard i ∈ S)
    (mu : StableExteriorIndex A S
      (nodesOfFourClusterPoint A hA vStar hcard)) :
    (p.toPolynomial * q.toPolynomial).eval (mu : ℝ) ≠ -(tau ^ 2) := by
  let nodes := nodesOfFourClusterPoint A hA vStar hcard
  let lambda : Fin 4 → ℝ := fun i ↦ (nodes i : ℝ)
  let m := Kstable + Kprod
  let L := 2 * m
  let P : ℕ → MonicQuadratic := fun k ↦ arnoldiFactorOrbit2 A v₀ k
  let Ps : ℕ → MonicQuadratic := fun k ↦ P (L + k)
  let sigma : ℕ → ℝ := fun k ↦ arnoldiNormalizerOrbit2 A v₀ (L + k)
  let H : ℝ := tau ^ 2
  let Q : Polynomial ℝ := p.toPolynomial * q.toPolynomial
  let Qs : ℕ → Polynomial ℝ := fun k ↦
    (Ps k).toPolynomial * (Ps (k + 1)).toPolynomial
  let defect : ℕ → ℝ := fun k ↦ H -
    Arnoldi.arnoldiHeightOrbit2 A v₀ (L + k)
  let exteriorWeight : ℕ → ℝ := fun k ↦
    weight A hA (arnoldiOrbit2 A v₀ (L + k)) mu
  let principalWeight : Fin 4 → ℕ → ℝ := fun i k ↦
    weight A hA (arnoldiOrbit2 A v₀ (L + k)) (nodes i)
  let denominator : ℕ → ℝ := fun k ↦ sigma k * sigma (k + 1)
  let exteriorMultiplier : ℕ → ℝ := fun k ↦
    |(Qs k).eval (mu : ℝ) / denominator k|
  let principalMultiplier : Fin 4 → ℕ → ℝ := fun i k ↦
    |(Qs k).eval (lambda i) / denominator k|
  let beta : Fin 4 → ℝ := Exterior.lagrangeWeight lambda (mu : ℝ)
  have hfactor : Q = FourNode.nodalQuartic lambda + C H := by
    simpa only [Q, H, nodes, lambda] using
      fourNode_factorization_of_mem_parityClusterSet
        A hA v₀ hv₀ hgrade₀ tau p q hp hq hnormalizer vStar
          (Or.inl hvStar) hcard
  have hLstable : Kstable ≤ L := by
    dsimp only [L, m]
    omega
  have hLprod : Kprod ≤ L := by
    dsimp only [L, m]
    omega
  have hsteps := arnoldiOrbit2_isQuadraticStepSequence_of_grade_three
    A hA v₀ hv₀ hgrade₀
  have hsigmaPos (k : ℕ) : 0 < sigma k := by
    exact hsteps.sigma_pos (L + k)
  have hcomponentExterior (k : ℕ) :
      component A hA (arnoldiOrbit2 A v₀ (L + k)) mu ≠ 0 :=
    component_ne_zero_of_mem_stable_active A hA v₀ hstable mu.property.1
      (hLstable.trans (Nat.le_add_right L k))
  have hcomponentPrincipal (i : Fin 4) (k : ℕ) :
      component A hA (arnoldiOrbit2 A v₀ (L + k)) (nodes i) ≠ 0 :=
    component_ne_zero_of_mem_stable_active A hA v₀ hstable
      (by simpa only [nodes] using hnodesStable i)
      (hLstable.trans (Nat.le_add_right L k))
  have hproductExterior (k : ℕ) : (Qs k).eval (mu : ℝ) ≠ 0 := by
    simpa only [Qs, Ps, P, show L + (k + 1) = L + k + 1 by omega] using
      twoStepProduct_eval_ne_zero_of_mem_stable
        A hA v₀ hstable mu mu.property.1 (L + k)
          (hLstable.trans (Nat.le_add_right L k))
  have hproductPrincipal (i : Fin 4) (k : ℕ) :
      (Qs k).eval (lambda i) ≠ 0 := by
    simpa only [Qs, Ps, P, lambda,
      show L + (k + 1) = L + k + 1 by omega] using
      twoStepProduct_eval_ne_zero_of_mem_stable
        A hA v₀ hstable (nodes i)
          (by simpa only [nodes] using hnodesStable i) (L + k)
          (hLstable.trans (Nat.le_add_right L k))
  have hupdate : Exterior.IsTwoStepSquaredWeightUpdate
      exteriorWeight principalWeight exteriorMultiplier principalMultiplier := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      dsimp only [exteriorWeight, weight]
      exact sq_pos_of_pos (norm_pos_iff.mpr (hcomponentExterior k))
    · intro i k
      dsimp only [principalWeight, weight]
      exact sq_pos_of_pos (norm_pos_iff.mpr (hcomponentPrincipal i k))
    · intro k
      dsimp only [exteriorMultiplier]
      rw [abs_pos]
      exact div_ne_zero (hproductExterior k)
        (mul_ne_zero (ne_of_gt (hsigmaPos k)) (ne_of_gt (hsigmaPos (k + 1))))
    · intro i k
      dsimp only [principalMultiplier]
      rw [abs_pos]
      exact div_ne_zero (hproductPrincipal i k)
        (mul_ne_zero (ne_of_gt (hsigmaPos k)) (ne_of_gt (hsigmaPos (k + 1))))
    · intro k
      have hrec := weight_arnoldiOrbit2_add_two A hA v₀ mu (L + k)
      simpa only [exteriorWeight, exteriorMultiplier, Qs, Ps, P, denominator,
        sigma, sq_abs, show L + k + 2 = L + (k + 2) by omega,
        show L + (k + 1) = L + k + 1 by omega] using hrec
    · intro i k
      have hrec := weight_arnoldiOrbit2_add_two A hA v₀ (nodes i) (L + k)
      simpa only [principalWeight, principalMultiplier, Qs, Ps, P, denominator,
        sigma, lambda, sq_abs, show L + k + 2 = L + (k + 2) by omega,
        show L + (k + 1) = L + k + 1 by omega] using hrec
  have hlambda : Function.Injective lambda := by
    intro i j hij
    apply nodesOfFourClusterPoint_injective A hA vStar hcard
    exact Subtype.ext hij
  have hdefectPos (k : ℕ) : 0 < defect k := by
    dsimp only [defect, H]
    exact sub_pos.mpr
      (arnoldiHeightOrbit2_lt_tau_sq_of_mem_stable_exterior
        A hA v₀ hv₀ hgrade₀ tau p q hp hq hnormalizer nodes hfactor
          hstable mu mu.property.1 mu.property.2 (L + k)
          (hLstable.trans (Nat.le_add_right L k)))
  have hdefectZero : Tendsto defect atTop (nhds 0) := by
    have hsigmaShift : Tendsto sigma atTop (nhds tau) := by
      simpa only [sigma, Function.comp_def, Nat.add_comm] using
        hnormalizer.comp (tendsto_add_atTop_nat L)
    have hsquare : Tendsto (fun k ↦ sigma k ^ 2) atTop (nhds (tau ^ 2)) :=
      hsigmaShift.pow 2
    have hsub : Tendsto (fun k ↦ tau ^ 2 - sigma k ^ 2) atTop (nhds 0) := by
      simpa only [sub_self] using
        (tendsto_const_nhds.sub hsquare : Tendsto
          (fun k ↦ tau ^ 2 - sigma k ^ 2) atTop
          (nhds (tau ^ 2 - tau ^ 2)))
    simpa only [defect, H, sigma, Arnoldi.arnoldiHeightOrbit2,
      quadraticStepHeight, sub_self] using hsub
  have htailShift (k : ℕ) :
      dist (Arnoldi.quadraticProductCoeff (Ps k) (Ps (k + 1)))
        (Arnoldi.quadraticProductCoeff p q) ≤ Ctail * defect k := by
    have ht := htail ((L - Kprod) + k)
    have hidx : (L - Kprod) + k + Kprod = L + k := by omega
    have hidx' : (L - Kprod) + k + Kprod + 1 = L + (k + 1) := by omega
    have hsucc : L + (k + 1) = L + k + 1 := by omega
    simpa only [Ps, P, defect, H, hidx, hidx', hsucc] using ht
  obtain ⟨B, hB, hlogError⟩ :=
    eventually_signed_logError_le_sq_of_productCoeff_tail
      Ps p q lambda hlambda (mu : ℝ) H Ctail defect
        (sq_pos_of_pos htau) hCtail (fun k ↦ (hdefectPos k).le)
        hdefectZero htailShift
  let logError : ℕ → ℝ := fun k ↦
    Real.log (1 - (Qs k - Q).eval (mu : ℝ) / H) +
      ∑ i : Fin 4, beta i *
        Real.log (1 + (Qs k - Q).eval (lambda i) / H)
  have hlogError' : ∀ᶠ k in atTop,
      |logError k| ≤ B * (defect k) ^ 2 := by
    simpa only [logError, Qs, Q, Ps, beta] using hlogError
  have hpositiveBase : ∀ᶠ k in atTop,
      0 < logError k - Real.log (1 - defect k / H) -
        Real.log (1 - defect (k + 1) / H) :=
    Exterior.eventually_pos_of_quadratic_logError
      defect logError H B (sq_pos_of_pos htau) hB hdefectPos
        hdefectZero hlogError'
  have hQeval (x : ℝ) : Tendsto (fun k ↦ (Qs k).eval x) atTop
      (nhds (Q.eval x)) := by
    have hglobal := Exterior.tendsto_quadraticProduct_eval_of_tendsto_coeff
      (P := arnoldiFactorOrbit2 A v₀)
      (Q := fun k ↦ arnoldiFactorOrbit2 A v₀ (k + 1))
      (p := p) (q := q) x hproduct
    have hshift := hglobal.comp (tendsto_add_atTop_nat L)
    simpa only [Qs, Ps, P, Q, Function.comp_def, Polynomial.eval_mul,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift
  have hQnode (i : Fin 4) : Q.eval (lambda i) = H := by
    simpa only [Q, H, lambda] using
      fourNode_product_eval_node_eq_tau_sq A nodes p q tau hfactor i
  have hpositiveOfNegative : Q.eval (mu : ℝ) = -H → ∀ᶠ k in atTop,
      0 < 2 * Real.log (exteriorMultiplier (2 * k)) +
        ∑ i, beta i * (2 * Real.log (principalMultiplier i (2 * k))) := by
    intro hnegative
    have hExteriorNeg : ∀ᶠ k in atTop, (Qs k).eval (mu : ℝ) < 0 :=
      (tendsto_order.1 (hQeval (mu : ℝ))).2 0 (by
        rw [hnegative]
        exact neg_neg_of_pos (sq_pos_of_pos htau))
    have hPrincipalPos : ∀ᶠ k in atTop, ∀ i, 0 < (Qs k).eval (lambda i) := by
      rw [Filter.eventually_all]
      intro i
      exact (tendsto_order.1 (hQeval (lambda i))).1 0 (by
        rw [hQnode i]
        exact sq_pos_of_pos htau)
    have hidentity : ∀ᶠ k in atTop,
        2 * Real.log (exteriorMultiplier k) +
            ∑ i, beta i * (2 * Real.log (principalMultiplier i k)) =
          2 * (logError k - Real.log (1 - defect k / H) -
            Real.log (1 - defect (k + 1) / H)) := by
      filter_upwards [hExteriorNeg, hPrincipalPos] with k hkExt hkPrincipal
      let f := Qs k - Q
      have hfExt : f.eval (mu : ℝ) = (Qs k).eval (mu : ℝ) + H := by
        dsimp only [f]
        rw [eval_sub, hnegative]
        ring
      have hfNode (i : Fin 4) :
          f.eval (lambda i) = (Qs k).eval (lambda i) - H := by
        dsimp only [f]
        rw [eval_sub, hQnode]
      have hextRatio : 0 < 1 - f.eval (mu : ℝ) / H := by
        have heq : 1 - f.eval (mu : ℝ) / H =
            (H - f.eval (mu : ℝ)) / H := by
          dsimp only [H]
          field_simp [ne_of_gt htau]
        rw [heq]
        exact div_pos (by rw [hfExt]; linarith) (sq_pos_of_pos htau)
      have hnodeRatio (i : Fin 4) :
          0 < 1 + f.eval (lambda i) / H := by
        have heq : 1 + f.eval (lambda i) / H =
            (H + f.eval (lambda i)) / H := by
          dsimp only [H]
          field_simp [ne_of_gt htau]
        rw [heq]
        have hnum : H + f.eval (lambda i) = (Qs k).eval (lambda i) := by
          rw [hfNode]
          ring
        rw [hnum]
        exact div_pos (hkPrincipal i) (sq_pos_of_pos htau)
      have hdenPos : 0 < denominator k :=
        mul_pos (hsigmaPos k) (hsigmaPos (k + 1))
      have hExtMultiplier : exteriorMultiplier k =
          (H - f.eval (mu : ℝ)) / denominator k := by
        dsimp only [exteriorMultiplier]
        rw [abs_div, abs_of_neg hkExt, abs_of_pos hdenPos, hfExt]
        ring
      have hPrincipalMultiplier (i : Fin 4) : principalMultiplier i k =
          (H + f.eval (lambda i)) / denominator k := by
        dsimp only [principalMultiplier]
        rw [abs_div, abs_of_pos (hkPrincipal i), abs_of_pos hdenPos,
          hfNode]
        ring
      have hid := normalized_lagrange_log_identity hlambda f (mu : ℝ) H
        (sigma k) (sigma (k + 1)) (sq_pos_of_pos htau)
          (hsigmaPos k) (hsigmaPos (k + 1)) hextRatio hnodeRatio
      rw [hExtMultiplier]
      simp_rw [hPrincipalMultiplier]
      simpa only [beta, logError, f, defect, H, sigma, denominator,
        Arnoldi.arnoldiHeightOrbit2, quadraticStepHeight] using hid
    have htwo : Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop := by
      apply tendsto_atTop.2
      intro N
      exact eventually_atTop.2 ⟨N, fun k hk ↦ by omega⟩
    filter_upwards [htwo.eventually hpositiveBase,
      htwo.eventually hidentity] with k hkPos hkIdentity
    rw [hkIdentity]
    linarith
  obtain ⟨phi, hphi, hcluster⟩ :=
    exists_shifted_subsequence_of_mem_evenClusterSet A v₀ vStar hvStar m
  have hexterior : Tendsto (fun j ↦ exteriorWeight (2 * phi j))
      atTop (nhds 0) := by
    have hcomponentStar : component A hA vStar mu = 0 := by
      rw [← not_ne_iff]
      intro hne
      have hactive : (mu : A.Eigenvalues) ∈ active A hA vStar :=
        (mem_active_iff A hA vStar mu).2 hne
      exact mu.property.2
        ((mem_range_nodesOfFourClusterPoint_iff A hA vStar hcard mu).2 hactive)
    have ht := (continuous_weight A hA mu).continuousAt.tendsto.comp hcluster
    simpa [Function.comp_def, exteriorWeight, L, weight, hcomponentStar,
      nodes, m] using ht
  let principalLimit : Fin 4 → ℝ := fun i ↦ weight A hA vStar (nodes i)
  have hprincipalLimitPos (i : Fin 4) : 0 < principalLimit i := by
    have hne : component A hA vStar (nodes i) ≠ 0 :=
      (mem_active_iff A hA vStar (nodes i)).1 (by
        simpa only [nodes] using
          nodesOfFourClusterPoint_mem_active A hA vStar hcard i)
    dsimp only [principalLimit, weight]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hprincipal (i : Fin 4) : Tendsto
      (fun j ↦ principalWeight i (2 * phi j)) atTop
      (nhds (principalLimit i)) := by
    have ht := (continuous_weight A hA (nodes i)).continuousAt.tendsto.comp hcluster
    simpa only [Function.comp_def, principalWeight, principalLimit, L, m] using ht
  exact Exterior.negativeNeutral_limit_ne_of_cocycle
    exteriorWeight principalWeight exteriorMultiplier principalMultiplier beta
      hupdate (Q.eval (mu : ℝ)) H 0 hpositiveOfNegative phi hphi
        hexterior principalLimit hprincipalLimitPos hprincipal

/-- A grade-four even cluster point gives one uniform geometric bound for
the total mass of all surviving exterior grouped eigenspaces.  This is the
finite exterior-subtype form of the manuscript's exterior-decay conclusion. -/
theorem stableExterior_geometric_of_fourNode_even_cluster
    (A : Module.End ℝ E) (hA : A.IsSymmetric) (v₀ : E)
    (hv₀ : ‖v₀‖ = 1) (hgrade₀ : 3 ≤ grade A v₀)
    (tau : ℝ) (htau : 0 < tau) (p q : MonicQuadratic)
    (Kprod : ℕ) (Ctail : ℝ) (hCtail : 0 ≤ Ctail)
    (hp : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n)).coeffPair)
      atTop (nhds p.coeffPair))
    (hq : Tendsto
      (fun n ↦ (arnoldiFactorOrbit2 A v₀ (2 * n + 1)).coeffPair)
      atTop (nhds q.coeffPair))
    (hnormalizer : Tendsto (arnoldiNormalizerOrbit2 A v₀)
      atTop (nhds tau))
    (hproduct : Tendsto (fun k ↦ Arnoldi.quadraticProductCoeff
      (arnoldiFactorOrbit2 A v₀ k)
      (arnoldiFactorOrbit2 A v₀ (k + 1))) atTop
      (nhds (Arnoldi.quadraticProductCoeff p q)))
    (htail : ∀ n, dist
      (Arnoldi.quadraticProductCoeff
        (arnoldiFactorOrbit2 A v₀ (n + Kprod))
        (arnoldiFactorOrbit2 A v₀ (n + Kprod + 1)))
      (Arnoldi.quadraticProductCoeff p q) ≤
        Ctail * (tau ^ 2 -
          Arnoldi.arnoldiHeightOrbit2 A v₀ (n + Kprod)))
    (Kstable : ℕ) (S : Finset A.Eigenvalues)
    (hstable : ∀ n, Kstable ≤ n →
      active A hA (arnoldiOrbit2 A v₀ n) = S)
    (vStar : E)
    (hvStar : vStar ∈ clusterSet
      (fun k ↦ arnoldiOrbit2 A v₀ (2 * k)))
    (hcard : (active A hA vStar).card = 4)
    (hnodesStable : ∀ i,
      nodesOfFourClusterPoint A hA vStar hcard i ∈ S) :
    ∃ C theta : ℝ, 0 < C ∧ 0 < theta ∧ theta < 1 ∧
      ∀ᶠ k in atTop,
        ∑ mu : StableExteriorIndex A S
            (nodesOfFourClusterPoint A hA vStar hcard),
          weight A hA (arnoldiOrbit2 A v₀ k) mu ≤ C * theta ^ k := by
  let nodes := nodesOfFourClusterPoint A hA vStar hcard
  let J := StableExteriorIndex A S nodes
  have hfactor : p.toPolynomial * q.toPolynomial =
      FourNode.nodalQuartic
          (fun i ↦ ((nodes i : A.Eigenvalues) : ℝ)) + C (tau ^ 2) := by
    simpa only [nodes] using fourNode_factorization_of_mem_parityClusterSet
      A hA v₀ hv₀ hgrade₀ tau p q hp hq hnormalizer vStar
        (Or.inl hvStar) hcard
  by_cases hJ : Nonempty J
  · letI : Nonempty J := hJ
    have hbound (j : J) :
        |(p.toPolynomial * q.toPolynomial).eval (j : ℝ)| ≤ tau ^ 2 :=
      fourNode_exterior_product_abs_le_tau_sq
        A hA v₀ hv₀ hgrade₀ tau htau p q hp hq hnormalizer hproduct
          nodes hfactor hstable j j.property.1 j.property.2
    have hnePositive (j : J) :
        (p.toPolynomial * q.toPolynomial).eval (j : ℝ) ≠ tau ^ 2 :=
      fourNode_exterior_product_ne_tau_sq A nodes p q tau hfactor
        j j.property.2
    have hneNegative (j : J) :
        (p.toPolynomial * q.toPolynomial).eval (j : ℝ) ≠ -(tau ^ 2) := by
      simpa only [J, nodes] using
        fourNode_stableExterior_product_ne_neg_tau_sq
          A hA v₀ hv₀ hgrade₀ tau htau p q Kprod Ctail hCtail hp hq
            hnormalizer hproduct htail Kstable S hstable vStar hvStar
              hcard hnodesStable j
    simpa only [J, nodes] using
      Exterior.arnoldiOrbit2_finite_exterior_mass_geometric_of_neutral_excluded
        A hA v₀ (fun j : J ↦ (j : A.Eigenvalues)) tau p q htau
          hnormalizer hproduct hbound hnePositive hneNegative
  · refine ⟨1, (1 : ℝ) / 2, by norm_num, by norm_num, by norm_num,
      Filter.Eventually.of_forall ?_⟩
    intro k
    change (∑ _j : J,
      weight A hA (arnoldiOrbit2 A v₀ k) _) ≤ 1 * ((1 : ℝ) / 2) ^ k
    have hsum : (∑ j : J,
        weight A hA (arnoldiOrbit2 A v₀ k) j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact (hJ ⟨j⟩).elim
    rw [hsum]
    positivity

end

end Spectral
end Forsythe
