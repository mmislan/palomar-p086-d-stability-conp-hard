module

public import proofs.DStabilityHardness.Symmetric

@[expose] public section

/-!
# Static classification of the core family and the contact (window-disk) bound

On the box `ρ ∈ [17/10, 7/4]`, `h ∈ [3, 5]`:
* `Kf ρ h ≥ 0` implies that `coreB ρ h` is D-stable;
* `Kf ρ h < 0` implies that `coreB ρ h` is strictly D-unstable;
* every imaginary-axis eigenvalue `iω` of a positive scaling with port rate `v` satisfies
  `k₂ (ω/v)² ≤ -Kf ρ h` (the contact height lies under the window semicircle).
-/

namespace DStabilityHardness

open DUnstableCores CollectiveInstability

noncomputable section

/-! ## Elementary positivity on the box -/

structure InBox (ρ h : ℝ) : Prop where
  ρ0 : 17 / 10 ≤ ρ
  ρ1 : ρ ≤ 7 / 4
  h0 : 3 ≤ h
  h1 : h ≤ 5

theorem e2_pos {ρ : ℝ} (hρ : 17 / 10 ≤ ρ) : 0 < e2 ρ := by unfold e2; linarith
theorem e3_pos {ρ : ℝ} (hρ : 17 / 10 ≤ ρ) : 0 < e3 ρ := by unfold e3; nlinarith
theorem k2_pos {ρ : ℝ} (hρ0 : 17 / 10 ≤ ρ) (hρ1 : ρ ≤ 7 / 4) : 0 < k2 ρ := by unfold k2; nlinarith
theorem m2_pos {h : ℝ} (hh : 3 ≤ h) : 0 < m2 h := by unfold m2; linarith
theorem m3_pos {ρ h : ℝ} (hρ : 17 / 10 ≤ ρ) (hh : 3 ≤ h) : 0 < m3 ρ h := by unfold m3; nlinarith
theorem m4_pos {ρ h : ℝ} (hρ : 17 / 10 ≤ ρ) (hh : 3 ≤ h) : 0 < m4 ρ h := by
  unfold m4 e3; nlinarith [sq_nonneg ρ, mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg ρ)]

theorem U_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 ≤ U x y z := by
  have : U x y z = x * (y - z) ^ 2 + y * (x - z) ^ 2 + z * (x - y) ^ 2 := by unfold U sp sq sr; ring
  rw [this]; positivity

theorem F0_pos {ρ x y z : ℝ} (hρ0 : 17 / 10 ≤ ρ) (hρ1 : ρ ≤ 7 / 4)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 < F0 ρ x y z := by
  have hr : 0 < sr x y z := by unfold sr; positivity
  have hU := U_nonneg hx.le hy.le hz.le
  have hk := k2_pos hρ0 hρ1
  rw [k2_eq] at hk
  have he2 := e2_pos hρ0
  have he3 := e3_pos hρ0
  unfold F0
  have hinner : 0 < e2 ρ * sp x y z * sq x y z - e3 ρ * sr x y z := by
    have : e2 ρ * sp x y z * sq x y z - e3 ρ * sr x y z =
        e2 ρ * U x y z + (9 * e2 ρ - e3 ρ) * sr x y z := by unfold U; ring
    rw [this]; positivity
  positivity

/-! ## The scaled coefficients are positive -/

theorem coeffs_pos {ρ h x y z v : ℝ} (hb : InBox ρ h) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hv : 0 < v) :
    0 < c1 ρ h x y z v ∧ 0 < c2 ρ h x y z v ∧ 0 < c3 ρ h x y z v ∧ 0 < c4 ρ h x y z v := by
  have := e2_pos hb.ρ0; have := e3_pos hb.ρ0; have := m2_pos hb.h0
  have := m3_pos hb.ρ0 hb.h0; have := m4_pos hb.ρ0 hb.h0
  have hh : 0 < h := by linarith [hb.h0]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [c1, c2, c3, c4, sp, sq, sr] <;> positivity

theorem delta3_pos {ρ h x y z v : ℝ} (hb : InBox ρ h) (hK : 0 ≤ Kf ρ h)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hv : 0 < v) :
    0 < hurwitzDelta (c1 ρ h x y z v) (c2 ρ h x y z v) (c3 ρ h x y z v) (c4 ρ h x y z v) := by
  rw [delta3_decomposition]
  have h0 := F0_pos (x := x) (y := y) (z := z) hb.ρ0 hb.ρ1 hx hy hz
  have h1 := F1_nonneg hb.ρ0 hb.ρ1 hb.h0 hb.h1 hx.le hy.le hz.le
  have h2 := F2_nonneg hb.ρ0 hb.ρ1 hb.h0 hb.h1 hx.le hy.le hz.le
  have hU := U_nonneg hx.le hy.le hz.le
  have hr : 0 < sr x y z := by unfold sr; positivity
  have := m2_pos hb.h0; have := m3_pos hb.ρ0 hb.h0
  have hh : 0 < h := by linarith [hb.h0]
  positivity

/-- Any positive rate vector on `Fin 4` is `![d 0, d 1, d 2, d 3]`. -/
theorem vec4_eta (d : Fin 4 → ℝ) : d = ![d 0, d 1, d 2, d 3] := by
  funext i; fin_cases i <;> rfl

/-- **Static stability.** -/
theorem static_dStable {ρ h : ℝ} (hb : InBox ρ h) (hK : 0 ≤ Kf ρ h) : DStable (coreB ρ h) := by
  intro d hd
  rw [vec4_eta d]
  obtain ⟨h1, h2, h3, h4⟩ := coeffs_pos (v := d 3) hb (hd 0) (hd 1) (hd 2) (hd 3)
  exact matrix_hurwitzStable_of_delta_pos (scaled_charpoly ρ h _ _ _ _) h1 h2 h3 h4
    (delta3_pos hb hK (hd 0) (hd 1) (hd 2) (hd 3))

/-- **Static strict instability.** Equal inner rates and a fast port. -/
theorem static_hurwitzUnstable {ρ h : ℝ} (hb : InBox ρ h) (hK : Kf ρ h < 0) :
    ∃ v : ℝ, 0 < v ∧ HurwitzUnstable (rightScale (coreB ρ h) ![1, 1, 1, v]) := by
  have hh : 0 < h := by linarith [hb.h0]
  set S := F0 ρ 1 1 1 + F1 ρ h 1 1 1 + F2 ρ h 1 1 1 with hS
  have h0 := F0_pos (x := 1) (y := 1) (z := 1) hb.ρ0 hb.ρ1 one_pos one_pos one_pos
  have h1 := F1_nonneg (x := 1) (y := 1) (z := 1) hb.ρ0 hb.ρ1 hb.h0 hb.h1 zero_le_one zero_le_one
    zero_le_one
  have h2 := F2_nonneg (x := 1) (y := 1) (z := 1) hb.ρ0 hb.ρ1 hb.h0 hb.h1 zero_le_one zero_le_one
    zero_le_one
  have hSpos : 0 < S := by rw [hS]; linarith
  have hhK : 0 < -(h * Kf ρ h) := by nlinarith
  set v := S / (-(h * Kf ρ h)) + 1 with hvdef
  have hv1 : 1 < v := by rw [hvdef]; have := div_pos hSpos hhK; linarith
  have hv : 0 < v := by linarith
  refine ⟨v, hv, ?_⟩
  obtain ⟨c1p, c2p, c3p, c4p⟩ := coeffs_pos (x := 1) (y := 1) (z := 1) (v := v) hb one_pos one_pos
    one_pos hv
  refine (matrix_unstable_of_delta_neg (scaled_charpoly ρ h 1 1 1 v) c1p c2p c3p c4p ?_).1
  rw [delta3_decomposition]
  have hU : U 1 1 1 = 0 := by unfold U sp sq sr; norm_num
  have hr : sr 1 1 1 = 1 := by unfold sr; norm_num
  rw [hU, hr]
  have hvS : S < v * (-(h * Kf ρ h)) := by
    have : S = (S / (-(h * Kf ρ h))) * (-(h * Kf ρ h)) := (div_mul_cancel₀ S (ne_of_gt hhK)).symm
    rw [hvdef]; nlinarith
  have hlow : F0 ρ 1 1 1 + F1 ρ h 1 1 1 * v + F2 ρ h 1 1 1 * v ^ 2 ≤ S * v ^ 2 := by
    rw [hS]
    have hv2 : 1 ≤ v ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hv1.le h1, mul_le_mul_of_nonneg_left hv2 h0.le]
  have : S * v ^ 2 + h * (m2 h * m3 ρ h * 0 + Kf ρ h * 1) * v ^ 3
      = v ^ 2 * (S - v * (-(h * Kf ρ h))) := by ring
  nlinarith [mul_neg_of_pos_of_neg (pow_pos hv 2) (sub_neg.mpr hvS)]

theorem static_dUnstable {ρ h : ℝ} (hb : InBox ρ h) (hK : Kf ρ h < 0) :
    DUnstable (coreB ρ h) := by
  obtain ⟨v, hv, hu⟩ := static_hurwitzUnstable hb hK
  refine ⟨![1, 1, 1, v], ?_, hu⟩
  intro i; fin_cases i <;> simp [hv]

/-! ## Contact bound -/

theorem quartic_axis_relations (a b c d ω : ℝ) (hω : ω ≠ 0)
    (hroot : quartic a b c d ((ω : ℂ) * Complex.I) = 0) :
    c = a * ω ^ 2 ∧ hurwitzDelta a b c d = 0 := by
  have him := congrArg Complex.im hroot
  have hre := congrArg Complex.re hroot
  simp [quartic, Complex.mul_re, Complex.mul_im, pow_succ] at him hre
  have hc : c = a * ω ^ 2 := by
    have hf : ω * (c - a * ω ^ 2) = 0 := by linear_combination him
    have := (mul_eq_zero.mp hf).resolve_left hω
    linarith
  refine ⟨hc, ?_⟩
  have hd : d = b * ω ^ 2 - ω ^ 4 := by linear_combination hre
  unfold hurwitzDelta; rw [hc, hd]; ring

/-- **Contact bound.** An imaginary-axis eigenvalue `iω` of a positive scaling, with port rate
`d 3`, has normalized port inverse rate `ω / d 3` under the window semicircle. -/
theorem contact_bound {ρ h : ℝ} (hb : InBox ρ h) (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i)
    (ω : ℝ) (hω : ω ≠ 0) (u : Fin 4 → ℂ)
    (heig : HasEigenpair (rightScale (coreB ρ h) d) ((ω : ℂ) * Complex.I) u) :
    k2 ρ * (ω / d 3) ^ 2 ≤ -Kf ρ h := by
  rw [vec4_eta d] at heig
  set x := d 0; set y := d 1; set z := d 2; set v := d 3
  have hx := hd 0; have hy := hd 1; have hz := hd 2; have hv : 0 < v := hd 3
  have hq := quartic_of_eigenpair (scaled_charpoly ρ h x y z v) heig
  obtain ⟨hc3, hΔ⟩ := quartic_axis_relations _ _ _ _ ω hω hq
  rw [delta3_decomposition] at hΔ
  have hh : 0 < h := by linarith [hb.h0]
  have hr : 0 < sr x y z := by unfold sr; positivity
  have hp : 0 < sp x y z := by unfold sp; positivity
  have h0 := F0_pos (x := x) (y := y) (z := z) hb.ρ0 hb.ρ1 hx hy hz
  have h1 := F1_nonneg hb.ρ0 hb.ρ1 hb.h0 hb.h1 hx.le hy.le hz.le
  have h2 := F2_nonneg hb.ρ0 hb.ρ1 hb.h0 hb.h1 hx.le hy.le hz.le
  have hP2 := Psi2_nonneg hb.ρ0 hb.ρ1 hb.h0 hb.h1 hx.le hy.le hz.le
  have hU := U_nonneg hx.le hy.le hz.le
  have he2 := e2_pos hb.ρ0; have he3 := e3_pos hb.ρ0
  have hm2 := m2_pos hb.h0; have hm3 := m3_pos hb.ρ0 hb.h0
  have hk := k2_pos hb.ρ0 hb.ρ1
  obtain ⟨c1p, -, -, -⟩ := coeffs_pos hb hx hy hz hv
  -- Ψ ≥ 0
  have hPsi : 0 ≤ c1 ρ h x y z v * (F0 ρ x y z + F1 ρ h x y z * v + F2 ρ h x y z * v ^ 2)
      - k2 ρ * h * sr x y z * v * c3 ρ h x y z v := by
    rw [psi_decomposition]
    have t1 : 0 ≤ sp x y z * F1 ρ h x y z + h * e2 ρ * e3 ρ * sr x y z * U x y z := by positivity
    positivity
  -- from Δ₃ = 0
  have hsum : F0 ρ x y z + F1 ρ h x y z * v + F2 ρ h x y z * v ^ 2
      ≤ -(h * Kf ρ h * sr x y z * v ^ 3) := by
    have : 0 ≤ h * (m2 h * m3 ρ h * U x y z) * v ^ 3 := by positivity
    nlinarith
  have hkey : k2 ρ * h * sr x y z * v * c3 ρ h x y z v
      ≤ c1 ρ h x y z v * (-(h * Kf ρ h * sr x y z * v ^ 3)) := by
    nlinarith [mul_le_mul_of_nonneg_left hsum c1p.le]
  rw [hc3] at hkey
  -- divide by c1 h r v > 0
  have hpos : 0 < c1 ρ h x y z v * h * sr x y z * v := by positivity
  have hmain : k2 ρ * ω ^ 2 ≤ -Kf ρ h * v ^ 2 := by
    have e : c1 ρ h x y z v * (-(h * Kf ρ h * sr x y z * v ^ 3)) =
        (c1 ρ h x y z v * h * sr x y z * v) * (-Kf ρ h * v ^ 2) := by ring
    have e' : k2 ρ * h * sr x y z * v * (c1 ρ h x y z v * ω ^ 2) =
        (c1 ρ h x y z v * h * sr x y z * v) * (k2 ρ * ω ^ 2) := by ring
    rw [e, e'] at hkey
    exact le_of_mul_le_mul_left hkey hpos
  rw [div_pow, mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  linarith

end

end DStabilityHardness
