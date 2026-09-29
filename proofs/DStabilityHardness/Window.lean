module

public import proofs.DStabilityHardness.Static
public import proofs.DStabilityCharacterization.FiniteRealization

@[expose] public section

/-!
# No imaginary-axis eigenvalues for window-avoiding partitions

Generic part: an eigenpair of a positively scaled attached matrix `attached B p r` with
`Re z ≥ 0` yields a static pencil eigenpair of `loadCore B p X`, `X = Σ staticLoad`, whose port
inverse rate is enlarged by the total lag `Σ lagShift` (absorption).

Family part: for the core `coreB ρ (hv ρ + 1/2)`, a total load `1`, and subset sums at distance
`≥ λ` from `1/2` with `4 W ≤ λ²` (`W` the squared window half-width), no positive scaling has an
eigenvalue on the imaginary axis.  The contradiction is between the contact bound (static contact
heights lie under the window semicircle) and the rounding bound (the attachments' total lag is at
least the distance from the effective static load to the nearest subset sum).
-/

namespace DStabilityHardness

open DUnstableCores CollectiveInstability DStabilityCharacterization.Granularity
open scoped BigOperators

noncomputable section

section Generic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Pencil form of an eigenpair of a right-scaled attached matrix. -/
theorem attached_pencil (B : Matrix ι ι ℝ) (p : ι) (r : κ → ℝ) (d : ι ⊕ κ → ℝ)
    (hd : ∀ i, 0 < d i) (z : ℂ) (u : ι ⊕ κ → ℂ)
    (hu : HasEigenpair (rightScale (attached B p r) d) z u) :
    ((fun i => (d (.inl i) : ℂ) * u (.inl i)) ≠ 0 ∨ (fun j => (d (.inr j) : ℂ) * u (.inr j)) ≠ 0) ∧
    (∀ i, (∑ j, (B i j : ℂ) * ((d (.inl j) : ℂ) * u (.inl j))) +
        (if i = p then ∑ j, (r j : ℂ) * ((d (.inr j) : ℂ) * u (.inr j)) else 0)
        = z * (((d (.inl i))⁻¹ : ℝ) : ℂ) * ((d (.inl i) : ℂ) * u (.inl i))) ∧
    (∀ j, (d (.inl p) : ℂ) * u (.inl p) - (d (.inr j) : ℂ) * u (.inr j)
        = z * (((d (.inr j))⁻¹ : ℝ) : ℂ) * ((d (.inr j) : ℂ) * u (.inr j))) := by
  set v : ι → ℂ := fun i => (d (.inl i) : ℂ) * u (.inl i) with hvdef
  set w : κ → ℂ := fun j => (d (.inr j) : ℂ) * u (.inr j) with hwdef
  have hdn (i : ι ⊕ κ) : (d i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd i))
  refine ⟨?_, ?_, ?_⟩
  · by_contra! h
    apply hu.1
    funext i
    cases i with
    | inl i => exact (mul_eq_zero.mp (congrFun h.1 i)).resolve_left (hdn (.inl i))
    | inr j => exact (mul_eq_zero.mp (congrFun h.2 j)).resolve_left (hdn (.inr j))
  · intro i
    have hi := hu.2 (.inl i)
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Fintype.sum_sum_type,
      attached, Complex.ofReal_mul] at hi
    have he : z * (((d (.inl i))⁻¹ : ℝ) : ℂ) * v i = z * u (.inl i) := by
      rw [hvdef]
      push_cast
      field_simp [hdn]
    change _ = z * (((d (.inl i))⁻¹ : ℝ) : ℂ) * v i
    rw [he]
    by_cases hip : i = p
    · simpa [hip, v, w, mul_assoc] using hi
    · simpa [hip, v, w, mul_assoc] using hi
  · intro j
    have hj := hu.2 (.inr j)
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Fintype.sum_sum_type,
      attached, Complex.ofReal_mul] at hj
    have he : z * (((d (.inr j))⁻¹ : ℝ) : ℂ) * w j = z * u (.inr j) := by
      rw [hwdef]
      push_cast
      field_simp [hdn]
    change v p - w j = z * (((d (.inr j))⁻¹ : ℝ) : ℂ) * w j
    rw [he]
    simpa [v, w, mul_assoc, sub_eq_add_neg, apply_ite (fun x : ℝ => (x : ℂ))] using hj

omit [DecidableEq κ] in
/-- Absorption turns the attached pencil into a static pencil at load `Σ staticLoad`. -/
theorem attached_static (B : Matrix ι ι ℝ) (p : ι) (r : κ → ℝ) (q : ι → ℝ) (t : κ → ℝ)
    (_hq : ∀ i, 0 < q i) (ht : ∀ j, 0 < t j) (z : ℂ) (hz : 0 ≤ z.re) (v : ι → ℂ) (w : κ → ℂ)
    (hn : v ≠ 0 ∨ w ≠ 0)
    (hc : ∀ i, (∑ j, (B i j : ℂ) * v j) + (if i = p then ∑ j, (r j : ℂ) * w j else 0)
      = z * (q i : ℂ) * v i)
    (hl : ∀ j, v p - w j = z * (t j : ℂ) * w j) :
    v ≠ 0 ∧ ∀ i, ∑ j, (loadCore B p (∑ k, staticLoad z (r k) (t k)) i j : ℂ) * v j
      = z * ((q i + if i = p then ∑ k, lagShift z (r k) (t k) else 0 : ℝ) : ℂ) * v i := by
  have hw : ∀ j, w j = v p / (1 + z * (t j : ℂ)) := by
    intro j
    apply (eq_div_iff (lag_den_ne hz (ht j))).mpr
    linear_combination -(hl j)
  have hv : v ≠ 0 := by
    intro h
    have hw0 : w = 0 := by ext j; simp [hw j, h]
    exact hn.elim (fun h' => h' h) (fun h' => h' hw0)
  refine ⟨hv, ?_⟩
  set x : ℝ := ∑ k, staticLoad z (r k) (t k)
  set a : ℝ := ∑ k, lagShift z (r k) (t k)
  have hsum : (∑ j, (r j : ℂ) * w j) + z * (a : ℂ) * v p = (x : ℂ) * v p := by
    have hh : ∀ j, (r j : ℂ) * w j + z * (lagShift z (r j) (t j) : ℂ) * v p =
        (staticLoad z (r j) (t j) : ℂ) * v p := by
      intro j
      rw [hw j]
      have h := congrArg (fun k : ℂ => k * v p) (absorption (r := r j) hz (ht j))
      convert h using 1
      ring
    have h := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hh j)
    simpa [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, x, a] using h
  intro i
  have hi := hc i
  simp only [loadCore, Complex.ofReal_add, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero,
    add_mul, Finset.sum_add_distrib]
  by_cases hip : i = p
  · subst i
    simp only [ite_true] at hi
    simp
    linear_combination hi - hsum
  · simpa [hip] using hi

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- A static pencil eigenpair is an eigenpair of the right-scaled matrix with inverse rates. -/
theorem eigenpair_of_pencil (A : Matrix ι ι ℝ) (q : ι → ℝ) (hq : ∀ i, 0 < q i) (z : ℂ)
    (v : ι → ℂ) (hv : v ≠ 0) (he : ∀ i, ∑ j, (A i j : ℂ) * v j = z * (q i : ℂ) * v i) :
    HasEigenpair (rightScale A (fun i => (q i)⁻¹)) z (fun i => (q i : ℂ) * v i) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply hv
    funext i
    have hi := congrFun h i
    have hqi : (q i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hq i))
    exact (mul_eq_zero.mp hi).resolve_left hqi
  · intro i
    change (∑ j, ((A i j * (q j)⁻¹ : ℝ) : ℂ) * ((q j : ℂ) * v j)) = z * ((q i : ℂ) * v i)
    have hh : ∀ j, ((A i j * (q j)⁻¹ : ℝ) : ℂ) * ((q j : ℂ) * v j) = (A i j : ℂ) * v j := by
      intro j
      have hqj : (q j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hq j))
      push_cast
      field_simp
    simp_rw [hh]
    rw [he i]
    ring

/-- On the imaginary axis the lag of a piece is the semicircle height of its load. -/
theorem axis_lag_sq (z : ℂ) (hz : z.re = 0) (r t : ℝ) :
    (z.im * lagShift z r t) ^ 2 = staticLoad z r t * (r - staticLoad z r t) := by
  have hd : denom z t = 1 + (z.im * t) ^ 2 := by unfold denom; rw [hz]; ring
  have hpos : 0 < denom z t := by rw [hd]; positivity
  unfold lagShift staticLoad
  rw [hz]
  field_simp
  rw [hd]
  ring

theorem axis_load_bounds (z : ℂ) (hz : z.re = 0) (r t : ℝ) (hr : 0 < r) :
    0 < staticLoad z r t ∧ staticLoad z r t ≤ r := by
  have hd : denom z t = 1 + (z.im * t) ^ 2 := by unfold denom; rw [hz]; ring
  have hpos : 0 < denom z t := by rw [hd]; positivity
  unfold staticLoad
  rw [hz]
  simp only [mul_zero, zero_mul, add_zero, mul_one]
  refine ⟨div_pos hr hpos, ?_⟩
  rw [div_le_iff₀ hpos, hd]
  nlinarith [sq_nonneg (z.im * t)]

/-- Rounding bound: the total lag dominates the distance of the static load to a subset sum. -/
theorem rounding_bound (z : ℂ) (hz : z.re = 0) (r t : κ → ℝ) (hr : ∀ j, 0 < r j)
    (ht : ∀ j, 0 < t j) :
    ∃ S : Finset κ, |(∑ k, staticLoad z (r k) (t k)) - ∑ j ∈ S, r j|
      ≤ |z.im| * ∑ k, lagShift z (r k) (t k) := by
  classical
  let x : κ → ℝ := fun k => staticLoad z (r k) (t k)
  let S : Finset κ := Finset.univ.filter (fun j => r j ≤ 2 * x j)
  refine ⟨S, ?_⟩
  have hsplit : (∑ k, x k) - ∑ j ∈ S, r j = ∑ k, (x k - if k ∈ S then r k else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter]
  change |(∑ k, x k) - ∑ j ∈ S, r j| ≤ _
  rw [hsplit, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro k _
  obtain ⟨hx0, hxr⟩ := axis_load_bounds z hz (r k) (t k) (hr k)
  have hsq := axis_lag_sq z hz (r k) (t k)
  have hlag : 0 ≤ lagShift z (r k) (t k) := (shift_pos hz.ge (hr k) (ht k)).le
  have key : (x k - if k ∈ S then r k else 0) ^ 2 ≤ (z.im * lagShift z (r k) (t k)) ^ 2 := by
    rw [hsq]
    change (x k - if k ∈ S then r k else 0) ^ 2 ≤ x k * (r k - x k)
    by_cases hk : k ∈ S
    · have hk' : r k ≤ 2 * x k := (Finset.mem_filter.mp hk).2
      rw [ite_eq_left hk]
      nlinarith
    · have hk' : ¬ r k ≤ 2 * x k := fun h => hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rw [ite_eq_right hk]
      push Not at hk'
      nlinarith
  have := sq_le_sq.mp key
  rwa [abs_mul, abs_of_nonneg hlag] at this

end Generic

section Family

abbrev port : Fin 4 := 3

theorem loadCore_coreB (ρ h x : ℝ) : loadCore (coreB ρ h) port x = coreB ρ (h - x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [loadCore, coreB, port]
  ring

/-- Squared half-width of the window `{Kf < 0}`. -/
def Wd (ρ : ℝ) : ℝ := (k1 ρ ^ 2 - 4 * k2 ρ * k0 ρ) / (4 * k2 ρ ^ 2)

theorem Kf_window (ρ h : ℝ) (hk : 0 < k2 ρ) : Kf ρ h = k2 ρ * ((h - hv ρ) ^ 2 - Wd ρ) := by
  rw [Kf_vertex ρ h hk.ne']
  unfold Wd
  field_simp

theorem hv_bounds {ρ : ℝ} (h0 : 17 / 10 ≤ ρ) (h1 : ρ ≤ 7 / 4) : 7 / 2 ≤ hv ρ ∧ hv ρ ≤ 9 / 2 := by
  have hk := k2_pos h0 h1
  unfold hv
  constructor
  · rw [le_div_iff₀ (by positivity)]
    unfold k1; unfold k2 at hk ⊢; nlinarith
  · rw [div_le_iff₀ (by positivity)]
    unfold k1; unfold k2 at hk ⊢; nlinarith

theorem Wd_le {ρ ρ₁ : ℝ} (h0 : 17 / 10 ≤ ρ) (h1 : ρ ≤ ρ₁) (h1' : ρ₁ ≤ 7 / 4) (h3 : 3 ≤ ρ₁ ^ 2) :
    Wd ρ ≤ 2304 / 625 * (ρ₁ ^ 2 - 3) := by
  have hk := k2_pos h0 (le_trans h1 h1')
  have hR : 2 / 5 + gam ρ ≤ 8 / 5 * k2 ρ := by
    unfold gam; unfold k2 at hk ⊢; nlinarith
  have hWd : Wd ρ = 36 / 25 * ((2 / 5 + gam ρ) / k2 ρ) ^ 2 * (ρ ^ 2 - 3) := by
    unfold Wd; rw [disc_factor]; field_simp; ring
  have hρρ : ρ ^ 2 ≤ ρ₁ ^ 2 := by nlinarith
  rcases le_or_gt 3 (ρ ^ 2) with h | h
  · have hR' : (2 / 5 + gam ρ) / k2 ρ ≤ 8 / 5 := by rw [div_le_iff₀ hk]; linarith
    have hR0 : 0 ≤ (2 / 5 + gam ρ) / k2 ρ := div_nonneg (by unfold gam; linarith) hk.le
    have hsq : ((2 / 5 + gam ρ) / k2 ρ) ^ 2 ≤ (8 / 5) ^ 2 := by nlinarith
    rw [hWd]; nlinarith
  · rw [hWd]
    have : 0 ≤ ((2 / 5 + gam ρ) / k2 ρ) ^ 2 := sq_nonneg _
    nlinarith

set_option maxHeartbeats 1000000 in
/-- **No imaginary-axis eigenvalues** for window-avoiding load vectors of total `1`. -/
theorem no_axis {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (ρ : ℝ)
    (hρ0 : 17 / 10 ≤ ρ) (hρ1 : ρ ≤ 7 / 4)
    (r : κ → ℝ) (hr : ∀ j, 0 < r j) (hG : ∑ j, r j = 1)
    (lam : ℝ) (hlam : 0 < lam) (hW : 4 * Wd ρ ≤ lam ^ 2)
    (hsub : ∀ S : Finset κ, lam ≤ |∑ j ∈ S, r j - 1 / 2|)
    (d : Fin 4 ⊕ κ → ℝ) (hd : ∀ i, 0 < d i) (z : ℂ) (u : Fin 4 ⊕ κ → ℂ)
    (hu : HasEigenpair (rightScale (attached (coreB ρ (hv ρ + 1 / 2)) port r) d) z u) :
    z.re ≠ 0 := by
  intro hz
  obtain ⟨hn, hc, hl⟩ := attached_pencil _ _ _ d hd z u hu
  let q : Fin 4 → ℝ := fun i => (d (.inl i))⁻¹
  let t : κ → ℝ := fun j => (d (.inr j))⁻¹
  have hq : ∀ i, 0 < q i := fun i => inv_pos.mpr (hd _)
  have ht : ∀ j, 0 < t j := fun j => inv_pos.mpr (hd _)
  obtain ⟨hv0, hst⟩ := attached_static (coreB ρ (hv ρ + 1 / 2)) port r q t hq ht z hz.ge _ _
    hn hc hl
  set v : Fin 4 → ℂ := fun i => (d (.inl i) : ℂ) * u (.inl i)
  set X : ℝ := ∑ k, staticLoad z (r k) (t k) with hXdef
  set a : ℝ := ∑ k, lagShift z (r k) (t k) with hadef
  have hX0 : 0 < X := Finset.sum_pos (fun j _ => (axis_load_bounds z hz (r j) (t j) (hr j)).1)
    Finset.univ_nonempty
  have hX1 : X ≤ 1 := by
    rw [← hG]
    exact Finset.sum_le_sum (fun j _ => (axis_load_bounds z hz (r j) (t j) (hr j)).2)
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun j _ => (shift_pos hz.ge (hr j) (ht j)).le)
  let q' : Fin 4 → ℝ := fun i => q i + if i = port then a else 0
  have hq' : ∀ i, 0 < q' i := by
    intro i; dsimp only [q']; split_ifs <;> linarith [hq i]
  obtain ⟨hvb0, hvb1⟩ := hv_bounds hρ0 hρ1
  set h := hv ρ + 1 / 2 - X with hhdef
  have hb : InBox ρ h := ⟨hρ0, hρ1, by linarith, by linarith⟩
  have he' : ∀ i, ∑ j, (coreB ρ h i j : ℂ) * v j = z * (q' i : ℂ) * v i := by
    intro i
    rw [hhdef, ← loadCore_coreB]
    exact hst i
  have heig := eigenpair_of_pencil (coreB ρ h) q' hq' z v hv0 he'
  have hd' : ∀ i, 0 < (fun i => (q' i)⁻¹) i := fun i => inv_pos.mpr (hq' i)
  by_cases hz0 : z = 0
  · rw [vec4_eta (fun i => (q' i)⁻¹)] at heig
    have hqz := quartic_of_eigenpair (scaled_charpoly ρ h _ _ _ _) heig
    rw [hz0] at hqz
    simp [quartic] at hqz
    obtain ⟨-, -, -, c4p⟩ := coeffs_pos hb (hd' 0) (hd' 1) (hd' 2) (hd' 3)
    exact absurd hqz (ne_of_gt c4p)
  · have hω : z.im ≠ 0 := fun h0 => hz0 (Complex.ext (by simp [hz]) (by simp [h0]))
    have hzI : z = (z.im : ℂ) * Complex.I := Complex.ext (by simp [hz]) (by simp)
    by_cases hK : 0 ≤ Kf ρ h
    · have := static_dStable hb hK _ hd' z _ heig
      linarith
    · push Not at hK
      rw [hzI] at heig
      have hcb := contact_bound hb _ hd' z.im hω _ heig
      have hk := k2_pos hρ0 hρ1
      rw [Kf_window ρ h hk] at hcb hK
      have hhv : h - hv ρ = 1 / 2 - X := by rw [hhdef]; ring
      rw [hhv] at hcb hK
      have hq3 : q' port = q port + a := by simp [q']
      have hwin : (1 / 2 - X) ^ 2 < Wd ρ := by
        by_contra hc
        push Not at hc
        have := mul_nonneg hk.le (sub_nonneg.mpr hc)
        linarith
      have hcon : (z.im * q' port) ^ 2 ≤ Wd ρ - (1 / 2 - X) ^ 2 := by
        have e : (z.im / (fun i => (q' i)⁻¹) 3) = z.im * q' port := by
          simp [div_inv_eq_mul]
        rw [e] at hcb
        have h2 : k2 ρ * (z.im * q' port) ^ 2 ≤ k2 ρ * (Wd ρ - (1 / 2 - X) ^ 2) := by linarith
        exact le_of_mul_le_mul_left h2 hk
      obtain ⟨S, hS⟩ := rounding_bound z hz r t hr ht
      have hsubS := hsub S
      have hd1 : |X - 1 / 2| < lam / 2 := by
        apply abs_lt_of_sq_lt_sq _ (by linarith)
        calc (X - 1 / 2) ^ 2 = (1 / 2 - X) ^ 2 := by ring
          _ < Wd ρ := hwin
          _ ≤ lam ^ 2 / 4 := by linarith
          _ = (lam / 2) ^ 2 := by ring
      have htri : |∑ j ∈ S, r j - 1 / 2| ≤ |X - ∑ j ∈ S, r j| + |X - 1 / 2| := by
        have := abs_sub_le (∑ j ∈ S, r j) X (1 / 2)
        rwa [abs_sub_comm (∑ j ∈ S, r j) X] at this
      have hlow : lam / 2 < |z.im| * a := by linarith
      have hA0 : 0 ≤ |z.im| * a := by positivity
      have hlow2 : lam ^ 2 / 4 < (|z.im| * a) ^ 2 := by nlinarith [hlow, hA0, hlam]
      have hωpos : 0 < z.im ^ 2 := by positivity
      have hsqA : (|z.im| * a) ^ 2 = z.im ^ 2 * a ^ 2 := by rw [mul_pow, sq_abs]
      have hqa : a ^ 2 < (q port + a) ^ 2 := by nlinarith [hq port, ha0]
      have hfin : z.im ^ 2 * a ^ 2 < z.im ^ 2 * (q port + a) ^ 2 :=
        mul_lt_mul_of_pos_left hqa hωpos
      have hcon' : z.im ^ 2 * (q port + a) ^ 2 ≤ Wd ρ := by
        rw [hq3, mul_pow] at hcon; linarith [sq_nonneg (1 / 2 - X)]
      linarith

end Family

end

end DStabilityHardness
