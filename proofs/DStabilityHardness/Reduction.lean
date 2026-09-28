module

public import proofs.DStabilityHardness.Window
public import proofs.DStabilityCharacterization.SpectralContinuation
public import proofs.DStabilityCharacterization.Threshold

@[expose] public section

/-!
# The PARTITION → D-stability reduction

For positive integer weights `w` with total `2T` and a Pell pair `p² = 3q² + 1` with `q ≥ 8T`,
`q ≥ 4`, the star matrix `hardMatrix p q w T` (core `coreB (p/q) (hv (p/q) + 1/2)`, loads
`w_j/(2T)` at the port) is D-stable iff no subset of `w` sums to `T`, and strictly D-unstable
otherwise.

* YES: the static load `1/2` sits at the window vertex, where the core is strictly unstable
  (`static_dUnstable`); a fast/slow realization of the subset (absorption identity) reproduces the
  unstable eigenvalue exactly (`reverse_absorption`).
* NO: along the path `ρ ∈ [17/10, p/q]` no positive scaling has an imaginary-axis eigenvalue
  (`no_axis`); at `ρ = 17/10 < √3` the static ray has no window, so the verified safety theorem
  (`attached_dStable_of_det`) supplies the Hurwitz base point; connectedness concludes.
-/

namespace DStabilityHardness

open DUnstableCores CollectiveInstability DStabilityCharacterization.Granularity
open DStabilityCharacterization.SpectralContinuation
open scoped BigOperators

noncomputable section

/-! ## Realizing a subset exactly (YES direction) -/

theorem subset_realization {κ : Type*} [Fintype κ] [DecidableEq κ] (z : ℂ) (hz : 0 < z.re)
    (G X q : ℝ) (hX : 0 < X) (hXG : X < G) (hq : 0 < q) (r : κ → ℝ) (hr : ∀ j, 0 < r j)
    (hrG : ∑ j, r j = G) (a : Finset κ) (ha : ∑ j ∈ a, r j = X) :
    ∃ t : κ → ℝ, (∀ j, 0 < t j) ∧ (∑ j, staticLoad z (r j) (t j)) = X ∧
      (∑ j, lagShift z (r j) (t j)) < q := by
  have hG : 0 < G := lt_trans hX hXG
  obtain ⟨δ, hd, hdq, hdG⟩ := small_delta z hz G X q hG hXG hq
  set f := staticLoad z 1 δ with hfdef
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hf := load_bounds hz.le hz0 (by norm_num : (0 : ℝ) < 1) hd
  have hdef := load_deficit_bound z hz.le δ hd
  rw [← hfdef] at hf hdef
  have hk : 0 < z.re ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.im]
  have hgap : 0 < G - X := sub_pos.mpr hXG
  have hN : 0 < X - X * f := by nlinarith [hf.2]
  have hNbound : X - X * f ≤ G * (z.re ^ 2 + z.im ^ 2) * δ ^ 2 := by
    have h1 : X * (1 - f) ≤ X * ((z.re ^ 2 + z.im ^ 2) * δ ^ 2) :=
      mul_le_mul_of_nonneg_left hdef hX.le
    have h2 : X * ((z.re ^ 2 + z.im ^ 2) * δ ^ 2) ≤ G * ((z.re ^ 2 + z.im ^ 2) * δ ^ 2) :=
      mul_le_mul_of_nonneg_right hXG.le (by positivity)
    nlinarith
  have hN1 : X - X * f < G - X := by linarith
  set y := (X - X * f) / (G - X) with hydef
  have hy : 0 < y := div_pos hN hgap
  have hy1 : y < 1 := (div_lt_one hgap).mpr hN1
  obtain ⟨T, hT, hTy⟩ := lag_surjective z hz y hy hy1
  let t : κ → ℝ := fun j => if j ∈ a then δ else T
  have ht : ∀ j, 0 < t j := by intro j; dsimp [t]; split_ifs <;> assumption
  have hNy : (G - X) * y = X - X * f := mul_div_cancel₀ _ (ne_of_gt hgap)
  have hload : (∑ j, staticLoad z (r j) (t j)) = X * f + (G - X) * y := by
    rw [show (∑ j, staticLoad z (r j) (t j)) = ∑ j, r j * staticLoad z 1 (t j) by
      apply Finset.sum_congr rfl
      intro j _
      exact load_linear z (r j) (t j)]
    have heq : ∀ j, staticLoad z 1 (t j) = if j ∈ a then f else y := by
      intro j
      dsimp [t]
      split_ifs <;> simp_all
    simp_rw [heq]
    have := sum_two_values a r f y
    rw [ha, hrG] at this
    exact this
  refine ⟨t, ht, by rw [hload, hNy]; ring, ?_⟩
  have hshift : (∑ j, lagShift z (r j) (t j)) ≤ X * δ + (G - X) * (y / (2 * z.re)) := by
    calc
      _ ≤ ∑ j, r j * (if j ∈ a then δ else y / (2 * z.re)) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j ∈ a
        · simpa [t, hj] using shift_le_time z hz.le (r j) δ (hr j).le hd
        · have hl := shift_le_load z hz (r j) T (hr j).le hT
          rw [load_linear z (r j) T, hTy] at hl
          simpa [t, hj, mul_div_assoc] using hl
      _ = _ := by
        have := sum_two_values a r δ (y / (2 * z.re))
        rw [ha, hrG] at this
        exact this
  have hslow : (G - X) * (y / (2 * z.re)) ≤ G * (z.re ^ 2 + z.im ^ 2) * δ ^ 2 / (2 * z.re) := by
    rw [← mul_div_assoc, hNy]
    exact div_le_div_of_nonneg_right hNbound (by positivity)
  have hfast : X * δ ≤ G * δ := mul_le_mul_of_nonneg_right hXG.le hd.le
  linarith

/-! ## Instance data -/

def hardLoads {κ : Type*} (w : κ → ℕ) (T : ℕ) : κ → ℝ := fun j => (w j : ℝ) / (2 * T)

/-- The reduction's output matrix. -/
def hardMatrix {κ : Type*} [DecidableEq κ] (p q : ℕ) (w : κ → ℕ) (T : ℕ) : Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) ℝ :=
  attached (coreB ((p : ℝ) / q) (hv ((p : ℝ) / q) + 1 / 2)) port (hardLoads w T)

/-! ## Pell arithmetic -/

theorem pell_facts (p q : ℕ) (hpell : p ^ 2 = 3 * q ^ 2 + 1) (hq4 : 4 ≤ q) :
    ((p : ℝ) / q) ^ 2 = 3 + 1 / (q : ℝ) ^ 2 ∧ 17 / 10 ≤ (p : ℝ) / q ∧ (p : ℝ) / q ≤ 7 / 4 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq4' : (4 : ℝ) ≤ q := by exact_mod_cast hq4
  have hp : ((p : ℝ)) ^ 2 = 3 * (q : ℝ) ^ 2 + 1 := by exact_mod_cast hpell
  have hsq : ((p : ℝ) / q) ^ 2 = 3 + 1 / (q : ℝ) ^ 2 := by
    rw [div_pow, hp]; field_simp
  have hρ0 : 0 ≤ (p : ℝ) / q := by positivity
  have hinv : 1 / (q : ℝ) ^ 2 ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hinv0 : 0 < 1 / (q : ℝ) ^ 2 := by positivity
  refine ⟨hsq, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-! ## The NO direction by continuation in `ρ` -/

theorem hv_continuousOn (ρ₁ : ℝ) (hρ1 : ρ₁ ≤ 7 / 4) : ContinuousOn hv (Set.Icc (17 / 10) ρ₁) := by
  unfold hv
  apply ContinuousOn.div
  · unfold k1; fun_prop
  · unfold k2; fun_prop
  · intro x hx
    have := k2_pos hx.1 (le_trans hx.2 hρ1)
    positivity

theorem path_continuousOn {κ : Type*} [Fintype κ] [DecidableEq κ] (ρ₁ : ℝ) (hρ1 : ρ₁ ≤ 7 / 4)
    (r : κ → ℝ) (d : Fin 4 ⊕ κ → ℝ) :
    ContinuousOn (fun ρ => rightScale (attached (coreB ρ (hv ρ + 1 / 2)) port r) d)
      (Set.Icc (17 / 10) ρ₁) := by
  have hhv := hv_continuousOn ρ₁ hρ1
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  simp only [rightScale]
  apply ContinuousOn.mul _ continuousOn_const
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [attached, coreB, gam] <;> fun_prop
  · exact continuousOn_const
  · exact continuousOn_const
  · exact continuousOn_const

/-- Static D-stability at every load of the ray when there is no window (`Wd ≤ 0`). -/
theorem no_window_static {ρ : ℝ} (hρ0 : 17 / 10 ≤ ρ) (hρ1 : ρ ≤ 7 / 4) (hW : Wd ρ ≤ 0)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    DStable (loadCore (coreB ρ (hv ρ + 1 / 2)) port x) := by
  rw [loadCore_coreB]
  obtain ⟨h0, h1⟩ := hv_bounds hρ0 hρ1
  have hb : InBox ρ (hv ρ + 1 / 2 - x) := ⟨hρ0, hρ1, by linarith, by linarith⟩
  apply static_dStable hb
  rw [Kf_window _ _ (k2_pos hρ0 hρ1)]
  have := k2_pos hρ0 hρ1
  have : 0 ≤ (hv ρ + 1 / 2 - x - hv ρ) ^ 2 - Wd ρ := by nlinarith [sq_nonneg (hv ρ + 1 / 2 - x - hv ρ)]
  positivity

theorem no_direction {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (ρ₁ : ℝ)
    (hρ10 : 17 / 10 ≤ ρ₁) (hρ1 : ρ₁ ≤ 7 / 4) (h3 : 3 ≤ ρ₁ ^ 2)
    (r : κ → ℝ) (hr : ∀ j, 0 < r j) (hG : ∑ j, r j = 1)
    (lam : ℝ) (hlam : 0 < lam) (hW : 4 * (2304 / 625 * (ρ₁ ^ 2 - 3)) ≤ lam ^ 2)
    (hsub : ∀ S : Finset κ, lam ≤ |∑ j ∈ S, r j - 1 / 2|) :
    DStable (attached (coreB ρ₁ (hv ρ₁ + 1 / 2)) port r) := by
  -- base point ρ₀ = 17/10 < √3: no window, safety theorem
  have hbase : DStable (attached (coreB (17 / 10) (hv (17 / 10) + 1 / 2)) port r) := by
    have hW0 : Wd (17 / 10) ≤ 0 := by
      unfold Wd; rw [disc_factor]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have : ((17 : ℝ) / 10) ^ 2 - 3 < 0 := by norm_num
      nlinarith [sq_nonneg (2 / 5 + gam (17 / 10))]
    apply attached_dStable_of_det _ _ r hr
    · intro x hx0 hx1
      rw [hG] at hx1
      exact no_window_static le_rfl (by norm_num) hW0 x hx0.le hx1.le
    · rw [hG]
      exact det_ne_zero_of_dStable _ (no_window_static le_rfl (by norm_num) hW0 1 zero_le_one le_rfl)
  intro d hd
  have hpath := hurwitzStable_on_preconnected (Set.Icc (17 / 10) ρ₁) isPreconnected_Icc
    (fun ρ => rightScale (attached (coreB ρ (hv ρ + 1 / 2)) port r) d)
    (path_continuousOn ρ₁ hρ1 r d)
    (by
      intro ρ hρ z v hv
      exact no_axis ρ hρ.1 (le_trans hρ.2 hρ1) r hr hG lam hlam
        (le_trans (by nlinarith [Wd_le hρ.1 hρ.2 hρ1 h3]) hW) hsub d hd z v hv)
    (17 / 10) ⟨le_rfl, hρ10⟩ (hbase d hd)
  exact hpath ρ₁ ⟨hρ10, le_rfl⟩

/-! ## Main theorem -/

theorem subset_gap {κ : Type*} (w : κ → ℕ) (T : ℕ) (hT : 0 < T) (S : Finset κ)
    (hS : ∑ j ∈ S, w j ≠ T) :
    1 / (2 * (T : ℝ)) ≤ |∑ j ∈ S, hardLoads w T j - 1 / 2| := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum : ∑ j ∈ S, hardLoads w T j = ((∑ j ∈ S, w j : ℕ) : ℝ) / (2 * T) := by
    unfold hardLoads; rw [← Finset.sum_div]; push_cast; rfl
  rw [hsum]
  have hne : ((∑ j ∈ S, w j : ℕ) : ℤ) ≠ (T : ℤ) := by exact_mod_cast hS
  have hint : (1 : ℝ) ≤ |((∑ j ∈ S, w j : ℕ) : ℝ) - T| := by
    have h1 : (1 : ℤ) ≤ |((∑ j ∈ S, w j : ℕ) : ℤ) - T| :=
      Int.one_le_abs (sub_ne_zero.mpr hne)
    have h2 : ((|((∑ j ∈ S, w j : ℕ) : ℤ) - T| : ℤ) : ℝ) = |((∑ j ∈ S, w j : ℕ) : ℝ) - T| := by
      push_cast; rfl
    rw [← h2]; exact_mod_cast h1
  have e : ((∑ j ∈ S, w j : ℕ) : ℝ) / (2 * T) - 1 / 2 =
      (((∑ j ∈ S, w j : ℕ) : ℝ) - T) / (2 * T) := by field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * T)]
  exact div_le_div_of_nonneg_right hint (by positivity)

/-- **T-HARD (mathematical core).** The reduction is correct: D-stable iff no subset sums to `T`;
strictly D-unstable otherwise. -/
theorem hardness_reduction {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (w : κ → ℕ) (hw : ∀ j, 0 < w j) (T : ℕ) (hT : ∑ j, w j = 2 * T)
    (p q : ℕ) (hpell : p ^ 2 = 3 * q ^ 2 + 1) (hq : 8 * T ≤ q) (hq4 : 4 ≤ q) :
    ((¬ ∃ S : Finset κ, ∑ j ∈ S, w j = T) → DStable (hardMatrix p q w T)) ∧
    ((∃ S : Finset κ, ∑ j ∈ S, w j = T) → DUnstable (hardMatrix p q w T)) := by
  obtain ⟨j0⟩ := (inferInstance : Nonempty κ)
  have hTpos : 0 < T := by
    have : w j0 ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j0)
    have := hw j0; omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  obtain ⟨hsq, hρ0, hρ1⟩ := pell_facts p q hpell hq4
  set ρ := (p : ℝ) / q with hρdef
  set r := hardLoads w T with hrdef
  have hr : ∀ j, 0 < r j := by
    intro j; rw [hrdef]; unfold hardLoads
    have : (0 : ℝ) < w j := by exact_mod_cast hw j
    positivity
  have hG : ∑ j, r j = 1 := by
    rw [hrdef]; unfold hardLoads
    rw [← Finset.sum_div]
    have : (∑ j, (w j : ℝ)) = 2 * T := by exact_mod_cast hT
    rw [this]; field_simp
  have hqr : (8 : ℝ) * T ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  constructor
  · intro hno
    have hsub : ∀ S : Finset κ, 1 / (2 * (T : ℝ)) ≤ |∑ j ∈ S, r j - 1 / 2| := by
      intro S
      exact subset_gap w T hTpos S (fun h => hno ⟨S, h⟩)
    have h3 : 3 ≤ ρ ^ 2 := by
      rw [hsq]; have : (0 : ℝ) < 1 / (q : ℝ) ^ 2 := by positivity
      linarith
    show DStable (attached (coreB ρ (hv ρ + 1 / 2)) port r)
    refine no_direction ρ hρ0 hρ1 h3 r hr hG (1 / (2 * T)) (by positivity) ?_ hsub
    rw [hsq]
    have hq2 : 64 * (T : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith
    rw [show (3 + 1 / (q : ℝ) ^ 2 - 3) = 1 / (q : ℝ) ^ 2 by ring, div_pow, one_pow,
      le_div_iff₀ (by positivity)]
    rw [show 4 * (2304 / 625 * (1 / (q : ℝ) ^ 2)) * (2 * T) ^ 2 = 36864 / 625 * T ^ 2 / (q : ℝ) ^ 2 by
      field_simp; ring]
    rw [div_le_one (by positivity)]
    nlinarith
  · rintro ⟨S, hS⟩
    -- static instability at the window vertex
    obtain ⟨h0, h1⟩ := hv_bounds hρ0 hρ1
    have hb : InBox ρ (hv ρ) := ⟨hρ0, hρ1, by linarith, by linarith⟩
    have hk := k2_pos hρ0 hρ1
    have hWpos : 0 < Wd ρ := by
      unfold Wd; rw [disc_factor, hsq]
      have : 0 < 2 / 5 + gam ρ := by unfold gam; linarith
      rw [show (3 + 1 / (q : ℝ) ^ 2 - 3) = 1 / (q : ℝ) ^ 2 by ring]
      apply div_pos (by positivity)
      have := hk
      positivity
    have hKneg : Kf ρ (hv ρ) < 0 := by
      rw [Kf_window _ _ hk]; simp; nlinarith
    have hun := static_dUnstable hb hKneg
    have hXv : hv ρ + 1 / 2 - 1 / 2 = hv ρ := by ring
    rw [← hXv, ← loadCore_coreB] at hun
    rcases hun with ⟨d, hd, z, u, hz, hu⟩
    let qq : Fin 4 → ℝ := fun i => (d i)⁻¹
    let v : Fin 4 → ℂ := fun i => (d i : ℂ) * u i
    have hdn (i : Fin 4) : (d i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd i))
    have hqq : ∀ i, 0 < qq i := fun i => inv_pos.mpr (hd i)
    have hv0 : v ≠ 0 := by
      intro h
      apply hu.1
      funext i
      exact (mul_eq_zero.mp (congrFun h i)).resolve_left (hdn i)
    have he : ∀ i, ∑ j, (loadCore (coreB ρ (hv ρ + 1 / 2)) port (1 / 2) i j : ℂ) * v j
        = z * (qq i : ℂ) * v i := by
      intro i
      have hi := hu.2 i
      simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Complex.ofReal_mul] at hi
      have heq : z * (qq i : ℂ) * v i = z * u i := by
        dsimp [qq, v]
        push_cast
        field_simp [hdn i]
      rw [heq]
      simpa [v, mul_assoc] using hi
    have hSr : ∑ j ∈ S, r j = 1 / 2 := by
      rw [hrdef]; unfold hardLoads
      rw [← Finset.sum_div]
      have : (∑ j ∈ S, (w j : ℝ)) = T := by exact_mod_cast hS
      rw [this]; field_simp
    obtain ⟨t, ht, hload, hshift⟩ := subset_realization z hz 1 (1 / 2) (qq port) (by norm_num)
      (by norm_num) (hqq port) r hr hG S hSr
    exact reverse_absorption _ port r t ht qq hqq z hz (1 / 2) v hv0 he hload hshift

/-- The biconditional form. -/
theorem hardness_iff {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (w : κ → ℕ) (hw : ∀ j, 0 < w j) (T : ℕ) (hT : ∑ j, w j = 2 * T)
    (p q : ℕ) (hpell : p ^ 2 = 3 * q ^ 2 + 1) (hq : 8 * T ≤ q) (hq4 : 4 ≤ q) :
    DStable (hardMatrix p q w T) ↔ ¬ ∃ S : Finset κ, ∑ j ∈ S, w j = T := by
  obtain ⟨hno, hyes⟩ := hardness_reduction w hw T hT p q hpell hq hq4
  constructor
  · intro hs hex
    obtain ⟨d, hd, z, u, hz, hu⟩ := hyes hex
    have := hs d hd z u hu
    linarith
  · exact hno

end

end DStabilityHardness
