module

public import proofs.DUnstableCores.Elementary.QuarticSpectral

@[expose] public section

/-!
# Exact spectral classification of positive-coefficient real quartics

For `p(z) = z^4 + a z^3 + b z^2 + c z + d` with `a,b,c,d > 0` and
`H = a b c - c^2 - a^2 d`:

* `H > 0`: every root has negative real part;
* `H = 0`: `p = (z^2 + w^2)(z^2 + a z + γ)` with `w, γ > 0`;
* `H < 0`: `p = ((z-t)^2 + w^2)(z^2 + β z + γ)` with `t, w, β, γ > 0`,
  i.e. exactly one conjugate pair lies in the open right half plane and the
  other pair is strictly stable.

The unstable case uses the constructive shift route: the Hurwitz determinant
of `p(z+t)` is negative at `t = 0` and positive at the explicit point
`t = 1 + c + d`, so the intermediate value theorem supplies a shift at which
`p(z+t)` has an imaginary pair.
-/

namespace CollectiveInstability

open DUnstableCores

/-- Monic real quartic evaluated on `ℂ`. -/
def quartic (a b c d : ℝ) (z : ℂ) : ℂ :=
  z ^ 4 + a * z ^ 3 + b * z ^ 2 + c * z + d

/-- The third Hurwitz determinant of the monic quartic. -/
def hurwitzDelta (a b c d : ℝ) : ℝ :=
  a * b * c - c ^ 2 - a ^ 2 * d

/-- A nonzero Hurwitz determinant excludes every imaginary-axis root. -/
theorem quartic_re_ne_zero {a b c d : ℝ} (hd : 0 < d)
    (hH : hurwitzDelta a b c d ≠ 0) {z : ℂ}
    (hz : quartic a b c d z = 0) : z.re ≠ 0 := by
  intro h0
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [quartic, pow_succ, Complex.mul_re, Complex.mul_im, h0] at hre him
  by_cases hy : z.im = 0
  · rw [hy] at hre
    norm_num at hre
    linarith
  · have hfac : z.im * (c - a * z.im ^ 2) = 0 := by linear_combination him
    have hc : c = a * z.im ^ 2 := by
      have := (mul_eq_zero.mp hfac).resolve_left hy
      linarith
    apply hH
    unfold hurwitzDelta
    rw [hc]
    linear_combination (-a ^ 2) * hre

/-- Positive Hurwitz determinant: every root is strictly stable. -/
theorem quartic_root_re_neg {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hH : 0 < hurwitzDelta a b c d) {z : ℂ}
    (hz : quartic a b c d z = 0) : z.re < 0 := by
  have hnot : ¬ 0 < z.re :=
    elementaryQuartic_no_rhp a b c d ha hb.le hc hd.le
      (by simpa [elementaryDelta, hurwitzDelta] using hH.le) z
      (by simpa [elementaryQuartic, quartic] using hz)
  have hne := quartic_re_ne_zero hd (ne_of_gt hH) hz
  rcases lt_trichotomy z.re 0 with h | h | h
  · exact h
  · exact absurd h hne
  · exact absurd h hnot

/-! ## The shift route -/

def shiftA (a : ℝ) (t : ℝ) : ℝ := a + 4 * t
def shiftB (a b : ℝ) (t : ℝ) : ℝ := b + 3 * a * t + 6 * t ^ 2
def shiftC (a b c : ℝ) (t : ℝ) : ℝ := c + 2 * b * t + 3 * a * t ^ 2 + 4 * t ^ 3
def shiftD (a b c d : ℝ) (t : ℝ) : ℝ := d + c * t + b * t ^ 2 + a * t ^ 3 + t ^ 4

/-- Hurwitz determinant of the shifted quartic `p(z+t)`. -/
def shiftH (a b c d : ℝ) (t : ℝ) : ℝ :=
  hurwitzDelta (shiftA a t) (shiftB a b t) (shiftC a b c t) (shiftD a b c d t)

theorem quartic_shift (a b c d t : ℝ) (u : ℂ) :
    quartic a b c d (u + t) =
      quartic (shiftA a t) (shiftB a b t) (shiftC a b c t) (shiftD a b c d t) u := by
  simp only [quartic, shiftA, shiftB, shiftC, shiftD]
  push_cast
  ring

theorem shiftH_zero (a b c d : ℝ) : shiftH a b c d 0 = hurwitzDelta a b c d := by
  simp [shiftH, shiftA, shiftB, shiftC, shiftD]

/-- Exact sum-of-nonnegative-blocks form of the shifted determinant. -/
theorem shiftH_blocks (a b c d t : ℝ) :
    shiftH a b c d t =
      a * b * c + 2 * a * (a * c + b ^ 2) * t
        + 4 * (2 * a ^ 2 * b + a * c + b ^ 2) * t ^ 2
        + 8 * a * (a ^ 2 + 4 * b) * t ^ 3 + 32 * b * t ^ 4
        + a ^ 2 * (48 * t ^ 4 - d) + 8 * a * t * (12 * t ^ 4 - d)
        + (32 * t ^ 6 - c ^ 2) + 16 * t ^ 2 * (2 * t ^ 4 - d) := by
  simp only [shiftH, hurwitzDelta, shiftA, shiftB, shiftC, shiftD]
  ring

/-- The explicit shift `1 + c + d` makes the Hurwitz determinant positive. -/
theorem shiftH_pos_explicit {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) : 0 < shiftH a b c d (1 + c + d) := by
  set T := 1 + c + d with hTdef
  have hT1 : 1 ≤ T := by linarith
  have hTc : c ≤ T := by linarith
  have hTd : d ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hT2 : T ≤ T ^ 2 := by nlinarith
  have hT4 : T ≤ T ^ 4 := by
    have : T ^ 2 ≤ T ^ 4 := by nlinarith [sq_nonneg T]
    linarith
  have hT6 : T ^ 2 ≤ T ^ 6 := by
    have h4 : 1 ≤ T ^ 4 := by nlinarith
    nlinarith [sq_nonneg T]
  have hd4 : d ≤ T ^ 4 := le_trans hTd hT4
  have hc2 : c ^ 2 ≤ T ^ 2 := by nlinarith
  have hc6 : c ^ 2 ≤ T ^ 6 := le_trans hc2 hT6
  rw [shiftH_blocks]
  have e1 : 0 < a * b * c := by positivity
  have e2 : 0 ≤ 2 * a * (a * c + b ^ 2) * T := by positivity
  have e3 : 0 ≤ 4 * (2 * a ^ 2 * b + a * c + b ^ 2) * T ^ 2 := by positivity
  have e4 : 0 ≤ 8 * a * (a ^ 2 + 4 * b) * T ^ 3 := by positivity
  have e5 : 0 ≤ 32 * b * T ^ 4 := by positivity
  have e6 : 0 ≤ a ^ 2 * (48 * T ^ 4 - d) :=
    mul_nonneg (sq_nonneg a) (by linarith)
  have e7 : 0 ≤ 8 * a * T * (12 * T ^ 4 - d) :=
    mul_nonneg (by positivity) (by linarith)
  have e8 : 0 ≤ 32 * T ^ 6 - c ^ 2 := by nlinarith
  have e9 : 0 ≤ 16 * T ^ 2 * (2 * T ^ 4 - d) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

theorem shiftH_continuous (a b c d : ℝ) : Continuous (shiftH a b c d) := by
  unfold shiftH hurwitzDelta shiftA shiftB shiftC shiftD
  fun_prop

/-- A shift annihilating the Hurwitz determinant factors the quartic into
a pair centred at `t` and a strictly stable quadratic. -/
theorem factor_of_shiftH_zero {a b c d t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (ht : 0 ≤ t) (hzero : shiftH a b c d t = 0) :
    ∃ w γ : ℝ, 0 < w ∧ 0 < γ ∧
      ∀ z : ℂ, quartic a b c d z =
        (z ^ 2 - 2 * t * z + (t ^ 2 + w ^ 2)) *
          (z ^ 2 + (a + 2 * t) * z + γ) := by
  have hA : 0 < shiftA a t := by unfold shiftA; positivity
  have hC : 0 < shiftC a b c t := by unfold shiftC; positivity
  set w : ℝ := Real.sqrt (shiftC a b c t / shiftA a t) with hwdef
  have hw2 : w ^ 2 = shiftC a b c t / shiftA a t :=
    Real.sq_sqrt (le_of_lt (div_pos hC hA))
  have hw : 0 < w := Real.sqrt_pos.mpr (div_pos hC hA)
  have hCeq : shiftC a b c t = shiftA a t * w ^ 2 := by
    rw [hw2]; field_simp
  have hDeq : shiftD a b c d t = shiftB a b t * w ^ 2 - w ^ 4 := by
    have hdelt : hurwitzDelta (shiftA a t) (shiftB a b t)
        (shiftC a b c t) (shiftD a b c d t) = 0 := hzero
    rw [hCeq] at hdelt
    have hfac : (shiftA a t) ^ 2 *
        (shiftB a b t * w ^ 2 - w ^ 4 - shiftD a b c d t) = 0 := by
      unfold hurwitzDelta at hdelt
      linear_combination hdelt
    have hn : (shiftA a t) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hA)
    have := (mul_eq_zero.mp hfac).resolve_left hn
    linarith
  set γ : ℝ := 3 * t ^ 2 + 2 * a * t + b - w ^ 2 with hγdef
  have e1 : c = -2 * t * γ + (t ^ 2 + w ^ 2) * (a + 2 * t) := by
    unfold shiftC shiftA at hCeq
    rw [hγdef]
    linear_combination hCeq
  have e2 : d = (t ^ 2 + w ^ 2) * γ := by
    unfold shiftC shiftA at hCeq
    unfold shiftD shiftB at hDeq
    rw [hγdef]
    linear_combination hDeq - t * hCeq
  have hγ : 0 < γ := by
    have hs : 0 < t ^ 2 + w ^ 2 := by positivity
    by_contra hneg
    have hneg' : γ ≤ 0 := le_of_not_gt hneg
    have : (t ^ 2 + w ^ 2) * γ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs.le hneg'
    linarith
  refine ⟨w, γ, hw, hγ, ?_⟩
  intro z
  simp only [quartic]
  rw [e1, e2, hγdef]
  push_cast
  ring

/-- Boundary case: `H = 0` gives an imaginary pair and a stable quadratic. -/
theorem quartic_boundary_factor {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hH : hurwitzDelta a b c d = 0) :
    ∃ w γ : ℝ, 0 < w ∧ 0 < γ ∧
      ∀ z : ℂ, quartic a b c d z = (z ^ 2 + w ^ 2) * (z ^ 2 + a * z + γ) := by
  obtain ⟨w, γ, hw, hγ, hfac⟩ :=
    factor_of_shiftH_zero (t := 0) ha hb hc hd le_rfl (by rw [shiftH_zero]; exact hH)
  refine ⟨w, γ, hw, hγ, fun z => ?_⟩
  rw [hfac z]
  push_cast
  ring

/-- Unstable case: `H < 0` gives exactly one open-right-half-plane pair. -/
theorem quartic_unstable_factor {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hH : hurwitzDelta a b c d < 0) :
    ∃ t w β γ : ℝ, 0 < t ∧ 0 < w ∧ 0 < β ∧ 0 < γ ∧
      ∀ z : ℂ, quartic a b c d z =
        (z ^ 2 - 2 * t * z + (t ^ 2 + w ^ 2)) * (z ^ 2 + β * z + γ) := by
  have hlo : shiftH a b c d 0 ≤ 0 := by rw [shiftH_zero]; exact hH.le
  have hhi : 0 ≤ shiftH a b c d (1 + c + d) :=
    (shiftH_pos_explicit ha hb hc hd).le
  have hle : (0 : ℝ) ≤ 1 + c + d := by linarith
  have hmem : (0 : ℝ) ∈ Set.Icc (shiftH a b c d 0) (shiftH a b c d (1 + c + d)) :=
    ⟨hlo, hhi⟩
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc hle
    (shiftH_continuous a b c d).continuousOn hmem
  have htpos : 0 < t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, shiftH_zero] at hzero
      linarith
    · exact h
  obtain ⟨w, γ, hw, hγ, hfac⟩ :=
    factor_of_shiftH_zero ha hb hc hd htpos.le hzero
  refine ⟨t, w, a + 2 * t, γ, htpos, hw, by linarith, hγ, fun z => ?_⟩
  rw [hfac z]
  push_cast
  ring

/-! ## Root consequences -/

theorem pair_root (t w : ℝ) :
    ((t : ℂ) + w * Complex.I) ^ 2 - 2 * t * ((t : ℂ) + w * Complex.I) +
      (t ^ 2 + w ^ 2) = 0 := by
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pair_roots_only {t w : ℝ} {z : ℂ}
    (hz : z ^ 2 - 2 * t * z + (t ^ 2 + w ^ 2) = 0) :
    z = (t : ℂ) + w * Complex.I ∨ z = (t : ℂ) - w * Complex.I := by
  have hprod : (z - ((t : ℂ) + w * Complex.I)) *
      (z - ((t : ℂ) - w * Complex.I)) = 0 := by
    ring_nf
    rw [Complex.I_sq]
    linear_combination hz
  rcases mul_eq_zero.mp hprod with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

/-- A real quadratic with positive coefficients has only stable roots. -/
theorem quadratic_roots_left {β γ : ℝ} (hβ : 0 < β)
    (hγ : 0 < γ) {z : ℂ} (hz : z ^ 2 + (β : ℂ) * z + (γ : ℂ) = 0) :
    z.re < 0 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    pow_two, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
    Complex.zero_im, zero_mul, sub_zero, add_zero] at hr hi
  by_cases hy : z.im = 0
  · rw [hy] at hr
    by_contra hx
    have hx0 : 0 ≤ z.re := le_of_not_gt hx
    have hax := mul_nonneg hβ.le hx0
    nlinarith [sq_nonneg z.re]
  · have he : z.im * (2 * z.re + β) = 0 := by nlinarith [hi]
    have he' := (mul_eq_zero.mp he).resolve_left hy
    linarith

/-- In the unstable case, the roots are exactly `t ± i w` (with `t > 0`)
together with two strictly stable roots, and `t + i w` is simple. -/
theorem quartic_unstable_roots {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hH : hurwitzDelta a b c d < 0) :
    ∃ t w : ℝ, 0 < t ∧ 0 < w ∧
      quartic a b c d ((t : ℂ) + w * Complex.I) = 0 ∧
      quartic a b c d ((t : ℂ) - w * Complex.I) = 0 ∧
      ∀ z : ℂ, quartic a b c d z = 0 →
        z = (t : ℂ) + w * Complex.I ∨ z = (t : ℂ) - w * Complex.I ∨ z.re < 0 := by
  obtain ⟨t, w, β, γ, ht, hw, hβ, hγ, hfac⟩ := quartic_unstable_factor ha hb hc hd hH
  refine ⟨t, w, ht, hw, ?_, ?_, ?_⟩
  · rw [hfac, pair_root, zero_mul]
  · rw [hfac]
    have : ((t : ℂ) - w * Complex.I) ^ 2 - 2 * t * ((t : ℂ) - w * Complex.I) +
        (t ^ 2 + w ^ 2) = 0 := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this, zero_mul]
  · intro z hz
    rw [hfac] at hz
    rcases mul_eq_zero.mp hz with h | h
    · rcases pair_roots_only h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · right; right
      exact quadratic_roots_left hβ hγ h

/-! ## Matrix consequences -/

open Polynomial

/-- A matrix whose characteristic polynomial is the given monic quartic. -/
def HasQuarticCharpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (a b c d : ℝ) : Prop :=
  A.charpoly = X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d

theorem quartic_of_eigenpair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {a b c d : ℝ} (hp : HasQuarticCharpoly A a b c d)
    {lam : ℂ} {v : ι → ℂ} (heig : HasEigenpair A lam v) :
    quartic a b c d lam = 0 := by
  have hroot := heig.isRoot_charpoly
  have hmap : (complexify A).charpoly = A.charpoly.map (algebraMap ℝ ℂ) := by
    have hmatrix : complexify A = A.map (algebraMap ℝ ℂ) := by
      ext i j
      rfl
    rw [hmatrix]
    exact Matrix.charpoly_map A (algebraMap ℝ ℂ)
  rw [hmap, hp] at hroot
  simpa [quartic] using hroot.eq_zero

theorem eigenpair_of_quartic_root {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {a b c d : ℝ} (hp : HasQuarticCharpoly A a b c d)
    {lam : ℂ} (hz : quartic a b c d lam = 0) :
    ∃ v : ι → ℂ, HasEigenpair A lam v := by
  have hmap : (complexify A).charpoly = A.charpoly.map (algebraMap ℝ ℂ) := by
    have hmatrix : complexify A = A.map (algebraMap ℝ ℂ) := by
      ext i j
      rfl
    rw [hmatrix]
    exact Matrix.charpoly_map A (algebraMap ℝ ℂ)
  apply hasEigenpair_of_isRoot_complexified_charpoly
  rw [hmap, hp]
  simpa [quartic] using hz

theorem matrix_hurwitzStable_of_delta_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {a b c d : ℝ} (hp : HasQuarticCharpoly A a b c d)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hH : 0 < hurwitzDelta a b c d) : HurwitzStable A := by
  intro lam v heig
  exact quartic_root_re_neg ha hb hc hd hH (quartic_of_eigenpair hp heig)

/-- Boundary: an imaginary eigenpair exists, and every eigenvalue off the
pair `±iw` is strictly stable. -/
theorem matrix_boundary_of_delta_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {a b c d : ℝ} (hp : HasQuarticCharpoly A a b c d)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hH : hurwitzDelta a b c d = 0) :
    ∃ w : ℝ, 0 < w ∧ (∃ v : ι → ℂ, HasEigenpair A ((w : ℂ) * Complex.I) v) ∧
      ∀ lam v, HasEigenpair A lam v →
        lam = (w : ℂ) * Complex.I ∨ lam = -((w : ℂ) * Complex.I) ∨ lam.re < 0 := by
  obtain ⟨w, γ, hw, hγ, hfac⟩ := quartic_boundary_factor ha hb hc hd hH
  refine ⟨w, hw, eigenpair_of_quartic_root hp ?_, ?_⟩
  · rw [hfac]
    have : ((w : ℂ) * Complex.I) ^ 2 + (w : ℂ) ^ 2 = 0 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [this, zero_mul]
  · intro lam v heig
    have hz := quartic_of_eigenpair hp heig
    rw [hfac] at hz
    rcases mul_eq_zero.mp hz with h | h
    · have hprod : (lam - (w : ℂ) * Complex.I) * (lam + (w : ℂ) * Complex.I) = 0 := by
        ring_nf; rw [Complex.I_sq]; linear_combination h
      rcases mul_eq_zero.mp hprod with h1 | h1
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h1))
    · right; right
      exact quadratic_roots_left ha hγ h

/-- Unstable: an open-right-half-plane eigenpair exists, the unstable
spectrum is exactly the pair `t ± i w`, and every other eigenvalue is
strictly stable. -/
theorem matrix_unstable_of_delta_neg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {a b c d : ℝ} (hp : HasQuarticCharpoly A a b c d)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hH : hurwitzDelta a b c d < 0) :
    HurwitzUnstable A ∧
      ∃ t w : ℝ, 0 < t ∧ 0 < w ∧
        (∃ v : ι → ℂ, HasEigenpair A ((t : ℂ) + w * Complex.I) v) ∧
        ∀ lam v, HasEigenpair A lam v →
          lam = (t : ℂ) + w * Complex.I ∨ lam = (t : ℂ) - w * Complex.I ∨
            lam.re < 0 := by
  obtain ⟨t, w, ht, hw, hroot, -, hall⟩ := quartic_unstable_roots ha hb hc hd hH
  obtain ⟨v, hv⟩ := eigenpair_of_quartic_root hp hroot
  refine ⟨⟨_, v, by simpa using ht, hv⟩, t, w, ht, hw, ⟨v, hv⟩, ?_⟩
  intro lam u heig
  exact hall lam (quartic_of_eigenpair hp heig)

end CollectiveInstability
