module

public import proofs.DUnstableCores.RouthHurwitzDim3

@[expose] public section

namespace DUnstableCores

def elementaryQuartic (a b c d : ℝ) (z : ℂ) : ℂ :=
  z^4 + a*z^3 + b*z^2 + c*z + d

def elementaryDelta (a b c d : ℝ) : ℝ := a*b*c-c^2-a^2*d

/-- The only quartic exclusion criterion needed by the elementary witness.
Strict positivity of a and c avoids degenerate Routh rows. -/
theorem elementaryQuartic_no_rhp (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 ≤ d)
    (hD : 0 ≤ elementaryDelta a b c d)
    (z : ℂ) (hz : elementaryQuartic a b c d z = 0) : ¬ 0 < z.re := by
  intro hx
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [elementaryQuartic, pow_succ, Complex.mul_re, Complex.mul_im] at hre him
  by_cases hy : z.im = 0
  · rw [hy] at hre
    norm_num at hre
    have hp : 0 < z.re^4 := pow_pos hx 4
    have hp1 : 0 ≤ a*z.re^3 := by positivity
    have hp2 : 0 ≤ b*z.re^2 := by positivity
    have hp3 : 0 ≤ c*z.re := by positivity
    nlinarith
  · let q := z.re^2+z.im^2
    let r := a+2*z.re
    let s := b+2*z.re*r-q
    have hi : z.im*(4*z.re^3-4*z.re*z.im^2+
        a*(3*z.re^2-z.im^2)+2*b*z.re+c)=0 := by nlinarith [him]
    have hib : 4*z.re^3-4*z.re*z.im^2+
        a*(3*z.re^2-z.im^2)+2*b*z.re+c=0 :=
      (mul_eq_zero.mp hi).resolve_left hy
    have hceq : c = -2*z.re*s+r*q := by dsimp [s,r,q]; nlinarith [hib]
    have hdeq : d = q*s := by
      have hix := congrArg (fun t : ℝ => z.re*t) hib
      dsimp [s,r,q]
      nlinarith [hre, hix]
    have hid : elementaryDelta a b c d =
        -2*z.re*r*((q-s)^2+a*c) := by
      rw [hdeq, hceq]
      dsimp [elementaryDelta,s,r,q]
      ring
    have hr : 0 < r := by dsimp [r]; positivity
    have hpos : 0 < (q-s)^2+a*c := by positivity
    have hneg : -2*z.re*r*((q-s)^2+a*c) < 0 := by
      have : 0 < 2*z.re*r*((q-s)^2+a*c) := by positivity
      nlinarith
    linarith [hid]

open Polynomial

def IsElementaryQuartic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (a b c d : ℝ) : Prop :=
  A.charpoly = X^4+C a*X^3+C b*X^2+C c*X+C d

theorem elementaryQuartic_matrix_nonpositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (a b c d : ℝ) (hp : IsElementaryQuartic A a b c d)
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 ≤ d)
    (hD : 0 ≤ elementaryDelta a b c d) : HurwitzNonpositive A := by
  rintro ⟨z,v,hz,heig⟩
  have hroot := heig.isRoot_charpoly
  have hmap : (complexify A).charpoly = A.charpoly.map (algebraMap ℝ ℂ) := by
    have hmatrix : complexify A = A.map (algebraMap ℝ ℂ) := by
      ext i j
      rfl
    rw [hmatrix]
    exact Matrix.charpoly_map A (algebraMap ℝ ℂ)
  rw [hmap, hp] at hroot
  have hzero : elementaryQuartic a b c d z = 0 := by
    simpa [elementaryQuartic] using hroot.eq_zero
  exact elementaryQuartic_no_rhp a b c d ha hb hc hd hD z hzero hz

def elementaryShiftA (x : ℝ) := 10908+4*x
def elementaryShiftB (x : ℝ) := 185600+3*10908*x+6*x^2
def elementaryShiftC (x : ℝ) := 1280000+2*185600*x+3*10908*x^2+4*x^3
def elementaryShiftD (x : ℝ) := 64000000+1280000*x+185600*x^2+10908*x^3+x^4
def elementaryShiftH (x : ℝ) := elementaryDelta
  (elementaryShiftA x) (elementaryShiftB x) (elementaryShiftC x) (elementaryShiftD x)

theorem elementary_exact_quartic_unstable_root :
    ∃ z : ℂ, 0 < z.re ∧ elementaryQuartic 10908 185600 1280000 64000000 z = 0 := by
  have hcont : Continuous elementaryShiftH := by
    unfold elementaryShiftH elementaryDelta elementaryShiftA elementaryShiftB
      elementaryShiftC elementaryShiftD
    fun_prop
  have hlo : elementaryShiftH 2 ≤ 0 := by
    norm_num [elementaryShiftH, elementaryDelta, elementaryShiftA,
      elementaryShiftB, elementaryShiftC, elementaryShiftD]
  have hhi : 0 ≤ elementaryShiftH 4 := by
    norm_num [elementaryShiftH, elementaryDelta, elementaryShiftA,
      elementaryShiftB, elementaryShiftC, elementaryShiftD]
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc (show (2:ℝ) ≤ 4 by norm_num)
    hcont.continuousOn ⟨hlo,hhi⟩
  have hxpos : 0 < x := by linarith [hx.1]
  have hA : 0 < elementaryShiftA x := by unfold elementaryShiftA; positivity
  have hC : 0 < elementaryShiftC x := by unfold elementaryShiftC; positivity
  let w : ℝ := Real.sqrt (elementaryShiftC x / elementaryShiftA x)
  have hw2 : w^2 = elementaryShiftC x / elementaryShiftA x :=
    Real.sq_sqrt (le_of_lt (div_pos hC hA))
  have hCeq : elementaryShiftC x = elementaryShiftA x*w^2 := by
    rw [hw2]; field_simp
  have hDeq : elementaryShiftD x = elementaryShiftB x*w^2-w^4 := by
    have hdelt : elementaryDelta (elementaryShiftA x) (elementaryShiftB x)
        (elementaryShiftC x) (elementaryShiftD x) = 0 := hzero
    rw [hCeq] at hdelt
    have hfac : (elementaryShiftA x)^2 *
        (elementaryShiftB x*w^2-w^4-elementaryShiftD x) = 0 := by
      dsimp [elementaryDelta] at hdelt
      nlinarith [hdelt]
    have hn : (elementaryShiftA x)^2 ≠ 0 := pow_ne_zero _ (ne_of_gt hA)
    have := (mul_eq_zero.mp hfac).resolve_left hn
    linarith
  have hroot : elementaryQuartic (elementaryShiftA x) (elementaryShiftB x)
      (elementaryShiftC x) (elementaryShiftD x) ((w:ℂ)*Complex.I) = 0 := by
    rw [hCeq,hDeq]
    apply Complex.ext <;>
      simp [elementaryQuartic, pow_succ, Complex.mul_re, Complex.mul_im] <;>
      ring
  refine ⟨(x:ℂ)+(w:ℂ)*Complex.I, by simpa using hxpos, ?_⟩
  calc
    elementaryQuartic 10908 185600 1280000 64000000 ((x:ℂ)+(w:ℂ)*Complex.I) =
        elementaryQuartic (elementaryShiftA x) (elementaryShiftB x)
          (elementaryShiftC x) (elementaryShiftD x) ((w:ℂ)*Complex.I) := by
      simp only [elementaryQuartic, elementaryShiftA, elementaryShiftB,
        elementaryShiftC, elementaryShiftD, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_ofNat]
      ring
    _ = 0 := hroot

theorem elementary_matrix_unstable
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hp : IsElementaryQuartic A 10908 185600 1280000 64000000) : HurwitzUnstable A := by
  obtain ⟨z,hz,hroot⟩ := elementary_exact_quartic_unstable_root
  have hmap : (complexify A).charpoly = A.charpoly.map (algebraMap ℝ ℂ) := by
    have hmatrix : complexify A = A.map (algebraMap ℝ ℂ) := by
      ext i j
      rfl
    rw [hmatrix]
    exact Matrix.charpoly_map A (algebraMap ℝ ℂ)
  have hr : (complexify A).charpoly.IsRoot z := by
    rw [hmap,hp]
    simpa [elementaryQuartic] using hroot
  obtain ⟨v,hv⟩ := hasEigenpair_of_isRoot_complexified_charpoly hr
  exact ⟨z,v,hz,hv⟩

end DUnstableCores
