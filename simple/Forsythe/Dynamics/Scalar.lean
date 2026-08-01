import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Scalar dynamics used by the four-node argument

The first group of results treats an inhomogeneous multiplicative recurrence
by dividing by the product of its positive multipliers.  The second records a
purely order-theoretic convergence criterion: a bounded real sequence cannot
have two limit points if every compact interior interval is eventually crossed
in at most one direction.
-/

set_option autoImplicit false

namespace Forsythe

open Filter Finset Set
open scoped Topology BigOperators

namespace ScalarDynamics

/-- Product of the first `n` multipliers. -/
def normalizedProduct (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ range n, m k

@[simp]
theorem normalizedProduct_zero (m : ℕ → ℝ) :
    normalizedProduct m 0 = 1 := by
  simp [normalizedProduct]

@[simp]
theorem normalizedProduct_succ (m : ℕ → ℝ) (n : ℕ) :
    normalizedProduct m (n + 1) = normalizedProduct m n * m n := by
  simp [normalizedProduct, prod_range_succ]

theorem normalizedProduct_pos {m : ℕ → ℝ} (hm : ∀ k, 0 < m k) (n : ℕ) :
    0 < normalizedProduct m n := by
  exact Finset.prod_pos fun k _ ↦ hm k

theorem normalizedProduct_ne_zero {m : ℕ → ℝ} (hm : ∀ k, 0 < m k) (n : ℕ) :
    normalizedProduct m n ≠ 0 :=
  ne_of_gt (normalizedProduct_pos hm n)

/-- Variation of constants for `alpha (k+1) = m k * alpha k + b k`. -/
theorem normalizedRecurrence_eq_partialSum
    {alpha m b : ℕ → ℝ} (hm : ∀ k, 0 < m k)
    (hrec : ∀ k, alpha (k + 1) = m k * alpha k + b k) (n : ℕ) :
    alpha n / normalizedProduct m n =
      alpha 0 + ∑ k ∈ range n, b k / normalizedProduct m (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hrec, sum_range_succ, normalizedProduct_succ]
      calc
        (m n * alpha n + b n) / (normalizedProduct m n * m n) =
            alpha n / normalizedProduct m n +
              b n / (normalizedProduct m n * m n) := by
          field_simp [normalizedProduct_ne_zero hm n, ne_of_gt (hm n)]
        _ = alpha 0 + ∑ k ∈ range n, b k / normalizedProduct m (k + 1) +
              b n / (normalizedProduct m n * m n) := by
          rw [ih]
        _ = alpha 0 + (∑ k ∈ range n, b k / normalizedProduct m (k + 1) +
              b n / (normalizedProduct m n * m n)) := by ring

/-- If the normalized forcing is summable, the product-normalized solution
converges. -/
theorem normalizedRecurrence_tendsto_of_summable
    {alpha m b : ℕ → ℝ} (hm : ∀ k, 0 < m k)
    (hrec : ∀ k, alpha (k + 1) = m k * alpha k + b k)
    (hs : Summable fun k ↦ b k / normalizedProduct m (k + 1)) :
    Tendsto (fun k ↦ alpha k / normalizedProduct m k) atTop
      (𝓝 (alpha 0 + ∑' k, b k / normalizedProduct m (k + 1))) := by
  have hsum := hs.hasSum.tendsto_sum_nat
  convert tendsto_const_nhds.add hsum using 1
  ext n
  exact normalizedRecurrence_eq_partialSum hm hrec n

/-- A geometric sequence divided by the product of positive multipliers
converging to one is summable.  This is the ratio-test step hidden in the
manuscript's product normalization. -/
theorem summable_geometric_div_normalizedProduct
    {m : ℕ → ℝ} (hmpos : ∀ k, 0 < m k)
    (hm : Tendsto m atTop (𝓝 1)) {theta : ℝ}
    (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1) :
    Summable fun k ↦ theta ^ k / normalizedProduct m (k + 1) := by
  let f : ℕ → ℝ := fun k ↦ theta ^ k / normalizedProduct m (k + 1)
  have hfpos : ∀ k, 0 < f k := fun k ↦ div_pos (pow_pos htheta_pos k)
    (normalizedProduct_pos hmpos (k + 1))
  have hratio : ∀ k, ‖f (k + 1)‖ / ‖f k‖ = theta / m (k + 1) := by
    intro k
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hfpos (k + 1)),
      abs_of_pos (hfpos k)]
    dsimp [f]
    rw [show normalizedProduct m (k + 1 + 1) =
      normalizedProduct m (k + 1) * m (k + 1) by
        exact normalizedProduct_succ m (k + 1)]
    field_simp [normalizedProduct_ne_zero hmpos (k + 1),
      normalizedProduct_ne_zero hmpos (1 + k), ne_of_gt (hmpos (k + 1)),
      ne_of_gt htheta_pos]
    rw [mul_div_cancel_right₀ _ (normalizedProduct_ne_zero hmpos (k + 1)), pow_succ]
  have hm' : Tendsto (fun k ↦ m (k + 1)) atTop (𝓝 1) :=
    hm.comp (tendsto_add_atTop_nat 1)
  have hratioT : Tendsto (fun k ↦ ‖f (k + 1)‖ / ‖f k‖) atTop (𝓝 theta) := by
    rw [show (fun k ↦ ‖f (k + 1)‖ / ‖f k‖) = (fun k ↦ theta / m (k + 1)) by
      funext k
      exact hratio k]
    have hconst : Tendsto (fun _ : ℕ ↦ theta) atTop (𝓝 theta) := tendsto_const_nhds
    have hdiv := hconst.div hm' (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun k ↦ theta / m (k + 1)) atTop (𝓝 (theta / 1)) at hdiv
    simpa only [div_one] using hdiv
  exact summable_of_ratio_test_tendsto_lt_one htheta_lt_one
    (Eventually.of_forall fun k ↦ ne_of_gt (hfpos k)) hratioT

/-- A raw geometric forcing remains summable after product normalization. -/
theorem summable_normalizedForcing_of_geometric
    {m b : ℕ → ℝ} (hmpos : ∀ k, 0 < m k)
    (hm : Tendsto m atTop (𝓝 1)) {C theta : ℝ}
    (_hC : 0 ≤ C) (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hb : ∀ k, |b k| ≤ C * theta ^ k) :
    Summable fun k ↦ b k / normalizedProduct m (k + 1) := by
  have hg := summable_geometric_div_normalizedProduct hmpos hm htheta_pos htheta_lt_one
  refine (hg.mul_left C).of_norm_bounded ?_
  intro k
  change |b k / normalizedProduct m (k + 1)| ≤
    C * (theta ^ k / normalizedProduct m (k + 1))
  rw [abs_div, abs_of_pos (normalizedProduct_pos hmpos (k + 1)),
    show C * (theta ^ k / normalizedProduct m (k + 1)) =
      (C * theta ^ k) / normalizedProduct m (k + 1) by ring]
  exact div_le_div_of_nonneg_right (hb k) (normalizedProduct_pos hmpos (k + 1)).le

/-- Product-normalized dichotomy for a geometrically forced recurrence.

If the normalized limit is zero, the solution is exactly the negative
normalized tail.  If it is nonzero, the solution is eventually one-signed
and the original geometric scale is negligible relative to it. -/
theorem normalizedRecurrence_dichotomy
    {alpha m b : ℕ → ℝ} (hmpos : ∀ k, 0 < m k)
    (hm : Tendsto m atTop (𝓝 1))
    (hrec : ∀ k, alpha (k + 1) = m k * alpha k + b k)
    {C theta : ℝ} (hC : 0 ≤ C) (htheta_pos : 0 < theta)
    (htheta_lt_one : theta < 1) (hb : ∀ k, |b k| ≤ C * theta ^ k) :
    ∃ L : ℝ,
      Tendsto (fun k ↦ alpha k / normalizedProduct m k) atTop (𝓝 L) ∧
      ((L = 0 ∧ ∀ k,
          alpha k = -normalizedProduct m k *
            ∑' j, b (j + k) / normalizedProduct m (j + k + 1)) ∨
        (L ≠ 0 ∧ (∀ᶠ k in atTop, 0 < L * alpha k) ∧
          Tendsto (fun k ↦ theta ^ k / |alpha k|) atTop (𝓝 0))) := by
  let e : ℕ → ℝ := fun k ↦ b k / normalizedProduct m (k + 1)
  have hs : Summable e :=
    summable_normalizedForcing_of_geometric hmpos hm hC htheta_pos htheta_lt_one hb
  let L : ℝ := alpha 0 + ∑' k, e k
  have hnorm : Tendsto (fun k ↦ alpha k / normalizedProduct m k) atTop (𝓝 L) := by
    dsimp [L, e]
    exact normalizedRecurrence_tendsto_of_summable hmpos hrec hs
  refine ⟨L, hnorm, ?_⟩
  by_cases hL : L = 0
  · left
    refine ⟨hL, fun k ↦ ?_⟩
    have hpartial := normalizedRecurrence_eq_partialSum hmpos hrec k
    have hsplit := hs.sum_add_tsum_nat_add k
    have hz : alpha k / normalizedProduct m k = -∑' j, e (j + k) := by
      dsimp [L] at hL
      rw [hpartial]
      linarith
    calc
      alpha k = normalizedProduct m k * (alpha k / normalizedProduct m k) := by
        field_simp [normalizedProduct_ne_zero hmpos k]
      _ = -normalizedProduct m k * ∑' j, e (j + k) := by rw [hz]; ring
      _ = -normalizedProduct m k *
          ∑' j, b (j + k) / normalizedProduct m (j + k + 1) := by rfl
  · right
    refine ⟨hL, ?_, ?_⟩
    · have hmul : Tendsto
          (fun k ↦ L * (alpha k / normalizedProduct m k)) atTop (𝓝 (L * L)) :=
        tendsto_const_nhds.mul hnorm
      have hev : ∀ᶠ k in atTop, 0 < L * (alpha k / normalizedProduct m k) :=
        hmul.eventually_const_lt (mul_self_pos.mpr hL)
      filter_upwards [hev] with k hk
      have hM := normalizedProduct_pos hmpos k
      calc
        0 < normalizedProduct m k * (L * (alpha k / normalizedProduct m k)) :=
          mul_pos hM hk
        _ = L * alpha k := by
          field_simp [normalizedProduct_ne_zero hmpos k]
    · have hg := summable_geometric_div_normalizedProduct hmpos hm
          htheta_pos htheta_lt_one
      have hg0 : Tendsto (fun k ↦ theta ^ k / normalizedProduct m (k + 1))
          atTop (𝓝 0) := hg.tendsto_atTop_zero
      have hshift0 : Tendsto (fun k ↦ theta ^ k / normalizedProduct m k)
          atTop (𝓝 0) := by
        have ht := hm.mul hg0
        convert ht using 1
        · ext k
          rw [normalizedProduct_succ]
          field_simp [normalizedProduct_ne_zero hmpos k, ne_of_gt (hmpos k)]
        · norm_num
      have habs : Tendsto (fun k ↦ |alpha k / normalizedProduct m k|)
          atTop (𝓝 |L|) := (continuous_abs.tendsto L).comp hnorm
      have hquot := hshift0.div habs (abs_ne_zero.mpr hL)
      convert hquot using 1
      · ext k
        change theta ^ k / |alpha k| =
          (theta ^ k / normalizedProduct m k) /
            |alpha k / normalizedProduct m k|
        rw [abs_div, abs_of_pos (normalizedProduct_pos hmpos k)]
        field_simp [normalizedProduct_ne_zero hmpos k]
      · norm_num

/-- The exact normalized tail in the zero-limit branch has the same geometric
rate as the forcing, up to a constant.  Positivity and `m k → 1` provide a
uniform lower bound `r` for the multipliers with `theta < r < 1`; the remaining
tail is then dominated by the geometric series with ratio `theta / r`. -/
theorem eventually_geometric_bound_of_normalizedTail
    {alpha m b : ℕ → ℝ} (hmpos : ∀ k, 0 < m k)
    (hm : Tendsto m atTop (𝓝 1)) {C theta : ℝ}
    (hC : 0 ≤ C) (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hb : ∀ k, |b k| ≤ C * theta ^ k)
    (htail : ∀ k,
      alpha k = -normalizedProduct m k *
        ∑' j, b (j + k) / normalizedProduct m (j + k + 1)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ k in atTop, |alpha k| ≤ C' * theta ^ k := by
  let r : ℝ := (theta + 1) / 2
  have htheta_r : theta < r := by dsimp [r]; linarith
  have hr_one : r < 1 := by dsimp [r]; linarith
  have hr_pos : 0 < r := htheta_pos.trans htheta_r
  have hq_nonneg : 0 ≤ theta / r := (div_pos htheta_pos hr_pos).le
  have hq_lt_one : theta / r < 1 := (div_lt_one hr_pos).2 htheta_r
  have hmLower : ∀ᶠ n in atTop, r ≤ m n :=
    ((tendsto_order.1 hm).1 r hr_one).mono fun _ hn ↦ hn.le
  obtain ⟨K, hK⟩ := eventually_atTop.1 hmLower
  let C' : ℝ := (C / r) * (1 - theta / r)⁻¹
  refine ⟨C', ?_, eventually_atTop.2 ⟨K, ?_⟩⟩
  · exact mul_nonneg (div_nonneg hC hr_pos.le)
      (inv_nonneg.mpr (sub_nonneg.mpr hq_lt_one.le))
  intro k hk
  let D : ℝ := C / r * theta ^ k
  have hD : 0 ≤ D := mul_nonneg (div_nonneg hC hr_pos.le) (pow_nonneg htheta_pos.le k)
  have hgeom : HasSum (fun j : ℕ ↦ D * (theta / r) ^ j)
      (D * (1 - theta / r)⁻¹) :=
    (hasSum_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left D
  have hterm : ∀ j : ℕ,
      ‖normalizedProduct m k *
          (b (j + k) / normalizedProduct m (j + k + 1))‖ ≤
        D * (theta / r) ^ j := by
    intro j
    let R : ℝ := ∏ x ∈ range (j + 1), m (k + x)
    have hRpos : 0 < R := by
      dsimp [R]
      exact Finset.prod_pos fun x _ ↦ hmpos (k + x)
    have hrpow_le : r ^ (j + 1) ≤ R := by
      dsimp [R]
      simpa only [Finset.prod_const, Finset.card_range] using
        (Finset.prod_le_prod (s := range (j + 1))
          (fun _ _ ↦ hr_pos.le) (fun x hx ↦ hK (k + x) (by omega)))
    have hprod_add : normalizedProduct m (k + (j + 1)) =
        normalizedProduct m k * R := by
      dsimp [normalizedProduct, R]
      exact Finset.prod_range_add m k (j + 1)
    have hratio_eq : normalizedProduct m k /
        normalizedProduct m (k + (j + 1)) = 1 / R := by
      rw [hprod_add]
      field_simp [normalizedProduct_ne_zero hmpos k, ne_of_gt hRpos]
    have hratio : normalizedProduct m k /
        normalizedProduct m (j + k + 1) ≤ 1 / r ^ (j + 1) := by
      rw [show j + k + 1 = k + (j + 1) by omega, hratio_eq]
      exact one_div_le_one_div_of_le (pow_pos hr_pos (j + 1)) hrpow_le
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (normalizedProduct_pos hmpos k),
      abs_of_pos (normalizedProduct_pos hmpos (j + k + 1))]
    calc
      normalizedProduct m k *
          (|b (j + k)| / normalizedProduct m (j + k + 1)) =
          |b (j + k)| *
            (normalizedProduct m k / normalizedProduct m (j + k + 1)) := by ring
      _ ≤ (C * theta ^ (j + k)) * (1 / r ^ (j + 1)) := by
        exact mul_le_mul (hb (j + k)) hratio
          (div_nonneg (normalizedProduct_pos hmpos k).le
            (normalizedProduct_pos hmpos (j + k + 1)).le)
          (mul_nonneg hC (pow_nonneg htheta_pos.le (j + k)))
      _ = D * (theta / r) ^ j := by
        dsimp only [D]
        simp only [div_eq_mul_inv, pow_add, pow_succ]
        ring_nf
  have hsumBound :
      ‖∑' j, normalizedProduct m k *
          (b (j + k) / normalizedProduct m (j + k + 1))‖ ≤
        D * (1 - theta / r)⁻¹ :=
    tsum_of_norm_bounded hgeom hterm
  calc
    |alpha k| =
        ‖∑' j, normalizedProduct m k *
          (b (j + k) / normalizedProduct m (j + k + 1))‖ := by
      rw [htail, tsum_mul_left]
      rw [Real.norm_eq_abs, neg_mul, abs_neg]
    _ ≤ D * (1 - theta / r)⁻¹ := hsumBound
    _ = C' * theta ^ k := by dsimp [C', D]; ring

/-- In the zero normalized-limit branch, a geometrically forced recurrence is
itself eventually geometrically small. -/
theorem normalizedRecurrence_zero_branch_geometric
    {alpha m b : ℕ → ℝ} (hmpos : ∀ k, 0 < m k)
    (hm : Tendsto m atTop (𝓝 1))
    (hrec : ∀ k, alpha (k + 1) = m k * alpha k + b k)
    {C theta : ℝ} (hC : 0 ≤ C) (htheta_pos : 0 < theta)
    (htheta_lt_one : theta < 1) (hb : ∀ k, |b k| ≤ C * theta ^ k)
    (hzero : Tendsto (fun k ↦ alpha k / normalizedProduct m k) atTop (𝓝 0)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ k in atTop, |alpha k| ≤ C' * theta ^ k := by
  obtain ⟨L, hL, hbranch⟩ := normalizedRecurrence_dichotomy hmpos hm hrec hC
    htheta_pos htheta_lt_one hb
  have hLzero : L = 0 := tendsto_nhds_unique hL hzero
  rcases hbranch with htail | hnonzero
  · exact eventually_geometric_bound_of_normalizedTail hmpos hm hC htheta_pos
      htheta_lt_one hb htail.2
  · exact (hnonzero.1 hLzero).elim

/-- Quantitative two-branch form used in the four-node closure argument.

In the zero branch it supplies both the exact tail formula and an eventual
geometric bound.  In the nonzero branch it supplies eventual sign stability
and says that the forcing scale is negligible compared with `|alpha k|`. -/
theorem normalizedRecurrence_geometric_dichotomy
    {alpha m b : ℕ → ℝ} (hmpos : ∀ k, 0 < m k)
    (hm : Tendsto m atTop (𝓝 1))
    (hrec : ∀ k, alpha (k + 1) = m k * alpha k + b k)
    {C theta : ℝ} (hC : 0 ≤ C) (htheta_pos : 0 < theta)
    (htheta_lt_one : theta < 1) (hb : ∀ k, |b k| ≤ C * theta ^ k) :
    ∃ L : ℝ,
      Tendsto (fun k ↦ alpha k / normalizedProduct m k) atTop (𝓝 L) ∧
      ((L = 0 ∧
          (∀ k, alpha k = -normalizedProduct m k *
            ∑' j, b (j + k) / normalizedProduct m (j + k + 1)) ∧
          ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ k in atTop, |alpha k| ≤ C' * theta ^ k) ∨
        (L ≠ 0 ∧ (∀ᶠ k in atTop, 0 < L * alpha k) ∧
          Tendsto (fun k ↦ theta ^ k / |alpha k|) atTop (𝓝 0))) := by
  obtain ⟨L, hL, hbranch⟩ := normalizedRecurrence_dichotomy hmpos hm hrec hC
    htheta_pos htheta_lt_one hb
  refine ⟨L, hL, ?_⟩
  rcases hbranch with hzero | hnonzero
  · left
    refine ⟨hzero.1, hzero.2, ?_⟩
    exact eventually_geometric_bound_of_normalizedTail hmpos hm hC htheta_pos
      htheta_lt_one hb hzero.2
  · exact Or.inr hnonzero

/-- On every compact subinterval of `(a,b)`, crossings are eventually
allowed in at most one direction. -/
def EventuallyOneWayCrossing (rho : ℕ → ℝ) (a b : ℝ) : Prop :=
  ∀ c d, a < c → c < d → d < b →
    (∃ N, ∀ i j, N ≤ i → i ≤ j → d < rho i → ¬ rho j < c) ∨
      (∃ N, ∀ i j, N ≤ i → i ≤ j → rho i < c → ¬ d < rho j)

/-- On each compact interval in `(a,b)`, all sufficiently late steps which
start in that interval have one fixed (but interval-dependent) direction. -/
def EventuallyLocallyDirectedSteps (rho : ℕ → ℝ) (a b : ℝ) : Prop :=
  ∀ c d, a < c → c < d → d < b →
    ((∀ᶠ k in atTop, rho k ∈ Icc c d → rho k ≤ rho (k + 1)) ∨
      (∀ᶠ k in atTop, rho k ∈ Icc c d → rho (k + 1) ≤ rho k))

/-- Vanishing steps turn a fixed local step direction into a no-return
crossing rule.  The slightly larger interval with endpoints
`(a+c)/2` and `(d+b)/2` absorbs the last step entering a crossing. -/
theorem eventuallyOneWayCrossing_of_eventuallyLocallyDirectedSteps
    {rho : ℕ → ℝ} {a b : ℝ}
    (hstep : Tendsto (fun k ↦ rho (k + 1) - rho k) atTop (𝓝 0))
    (hdir : EventuallyLocallyDirectedSteps rho a b) :
    EventuallyOneWayCrossing rho a b := by
  intro c d hac hcd hdb
  let c₀ : ℝ := (a + c) / 2
  let d₀ : ℝ := (d + b) / 2
  have hac₀ : a < c₀ := by dsimp [c₀]; linarith
  have hc₀c : c₀ < c := by dsimp [c₀]; linarith
  have hc₀d₀ : c₀ < d₀ := by dsimp [c₀, d₀]; linarith
  have hdd₀ : d < d₀ := by dsimp [d₀]; linarith
  have hd₀b : d₀ < b := by dsimp [d₀]; linarith
  rcases hdir c₀ d₀ hac₀ hc₀d₀ hd₀b with hinc | hdec
  · left
    have hlower : ∀ᶠ k in atTop,
        -(d₀ - c) < rho (k + 1) - rho k :=
      (tendsto_order.1 hstep).1 _ (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hinc.and hlower)
    refine ⟨N, ?_⟩
    intro i j hiN hij hi
    have hstay : c < rho j := by
      induction j, hij using Nat.le_induction with
      | base => exact hcd.trans hi
      | succ j hij ih =>
          have hj := hN j (hiN.trans hij)
          by_cases hjd₀ : rho j ≤ d₀
          · exact ih.trans_le (hj.1 ⟨hc₀c.le.trans ih.le, hjd₀⟩)
          · have : d₀ < rho j := lt_of_not_ge hjd₀
            linarith [hj.2]
    exact fun hj ↦ (not_lt_of_ge hstay.le) hj
  · right
    have hupper : ∀ᶠ k in atTop,
        rho (k + 1) - rho k < d - c₀ :=
      (tendsto_order.1 hstep).2 _ (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hdec.and hupper)
    refine ⟨N, ?_⟩
    intro i j hiN hij hi
    have hstay : rho j < d := by
      induction j, hij using Nat.le_induction with
      | base => exact hi.trans hcd
      | succ j hij ih =>
          have hj := hN j (hiN.trans hij)
          by_cases hc₀j : c₀ ≤ rho j
          · exact (hj.1 ⟨hc₀j, ih.le.trans hdd₀.le⟩).trans_lt ih
          · have : rho j < c₀ := lt_of_not_ge hc₀j
            linarith [hj.2]
    exact fun hj ↦ (not_lt_of_ge hstay.le) hj

/-- A sequence confined to a compact interval and eventually crossing each
compact interior subinterval in at most one direction converges. -/
theorem tendsto_of_eventuallyOneWayCrossing
    {rho : ℕ → ℝ} {a b : ℝ} (hrho : ∀ k, rho k ∈ Icc a b)
    (hcross : EventuallyOneWayCrossing rho a b) :
    ∃ l ∈ Icc a b, Tendsto rho atTop (𝓝 l) := by
  have habove : IsBoundedUnder (· ≤ ·) atTop rho :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun k ↦ (hrho k).2)
  have hbelow : IsBoundedUnder (· ≥ ·) atTop rho :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun k ↦ (hrho k).1)
  have hno : ∀ c ∈ (univ : Set ℝ), ∀ d ∈ (univ : Set ℝ), c < d →
      ¬((∃ᶠ k in atTop, rho k < c) ∧ ∃ᶠ k in atTop, d < rho k) := by
    intro c _ d _ hcd
    rintro ⟨hlow, hhigh⟩
    by_cases hca : c ≤ a
    · obtain ⟨k, hk⟩ := hlow.exists
      exact (not_lt_of_ge (hca.trans (hrho k).1)) hk
    by_cases hbd : b ≤ d
    · obtain ⟨k, hk⟩ := hhigh.exists
      exact (not_lt_of_ge ((hrho k).2.trans hbd)) hk
    have hac : a < c := lt_of_not_ge hca
    have hdb : d < b := lt_of_not_ge hbd
    rcases hcross c d hac hcd hdb with hdown | hup
    · rcases hdown with ⟨N, hN⟩
      rw [frequently_atTop] at hlow hhigh
      obtain ⟨i, hiN, hi⟩ := hhigh N
      obtain ⟨j, hij, hj⟩ := hlow i
      exact hN i j hiN hij hi hj
    · rcases hup with ⟨N, hN⟩
      rw [frequently_atTop] at hlow hhigh
      obtain ⟨i, hiN, hi⟩ := hlow N
      obtain ⟨j, hij, hj⟩ := hhigh i
      exact hN i j hiN hij hi hj
  obtain ⟨l, hl⟩ := tendsto_of_no_upcrossings (s := (univ : Set ℝ))
    dense_univ hno habove hbelow
  refine ⟨l, ?_, hl⟩
  exact isClosed_Icc.mem_of_tendsto hl (Eventually.of_forall hrho)

/-- Manuscript-facing one-way-crossing criterion.  A bounded interval
sequence converges if its steps vanish and late steps starting in each compact
interior interval all point in one direction. -/
theorem tendsto_of_eventuallyLocallyDirectedSteps
    {rho : ℕ → ℝ} {a b : ℝ} (hrho : ∀ k, rho k ∈ Icc a b)
    (hstep : Tendsto (fun k ↦ rho (k + 1) - rho k) atTop (𝓝 0))
    (hdir : EventuallyLocallyDirectedSteps rho a b) :
    ∃ l ∈ Icc a b, Tendsto rho atTop (𝓝 l) :=
  tendsto_of_eventuallyOneWayCrossing hrho
    (eventuallyOneWayCrossing_of_eventuallyLocallyDirectedSteps hstep hdir)

end ScalarDynamics

end Forsythe
