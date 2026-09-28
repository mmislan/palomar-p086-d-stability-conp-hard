module

public import proofs.DUnstableCores.DScaling

@[expose] public section
set_option maxHeartbeats 40000

/-! Coordinate-port absorption on the entire closed right half-plane.
The final theorem uses literal matrix eigenpairs, with arbitrary finite cores and leaves.
-/
namespace DStabilityCharacterization.Granularity
open DUnstableCores
open scoped BigOperators
noncomputable section

def denom (z : ℂ) (t : ℝ) : ℝ := (1 + z.re*t)^2 + (z.im*t)^2
def lagShift (z : ℂ) (r t : ℝ) : ℝ := r*t / denom z t
def staticLoad (z : ℂ) (r t : ℝ) : ℝ := r*(1+2*z.re*t) / denom z t

theorem denom_pos {z : ℂ} {t : ℝ} (hz : 0 ≤ z.re) (ht : 0<t) :
    0 < denom z t := by
  have h : 0 ≤ z.re*t := mul_nonneg hz ht.le
  unfold denom
  nlinarith [sq_nonneg (z.im*t)]

theorem load_bounds {z : ℂ} {r t : ℝ} (hz : 0 ≤ z.re) (hne : z ≠ 0)
    (hr : 0<r) (ht : 0<t) : 0 < staticLoad z r t ∧ staticLoad z r t < r := by
  have hd := denom_pos hz ht
  have hn : 0 < z.re^2+z.im^2 := by
    by_contra! h
    have h1 : z.re=0 := by nlinarith [sq_nonneg z.im, sq_nonneg z.re]
    have h2 : z.im=0 := by nlinarith [sq_nonneg z.im, sq_nonneg z.re]
    exact hne (Complex.ext h1 h2)
  constructor
  · exact div_pos (mul_pos hr (by nlinarith [mul_nonneg hz ht.le])) hd
  · rw [staticLoad, div_lt_iff₀ hd]
    have hh := mul_pos (mul_pos hr hn) (sq_pos_of_pos ht)
    unfold denom
    nlinarith

theorem shift_pos {z : ℂ} {r t : ℝ} (hz : 0 ≤ z.re) (hr : 0<r) (ht : 0<t) :
    0 < lagShift z r t := div_pos (mul_pos hr ht) (denom_pos hz ht)

theorem absorption {z : ℂ} {r t : ℝ} (hz : 0 ≤ z.re) (ht : 0<t) :
    (r : ℂ) / (1+z*t) + z*(lagShift z r t : ℂ) = (staticLoad z r t : ℂ) := by
  have hd := ne_of_gt (denom_pos hz ht)
  have hre : ((r : ℂ)/(1+z*t)).re = r*(1+z.re*t)/denom z t := by
    simp [Complex.div_re, Complex.normSq_apply, denom, pow_two]
  have him : ((r : ℂ)/(1+z*t)).im = -(r*(z.im*t))/denom z t := by
    simp [Complex.div_im, Complex.normSq_apply, denom, pow_two, neg_div]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, hre]
    unfold lagShift staticLoad
    field_simp
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, him]
    unfold lagShift
    ring

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def loadCore (B : Matrix ι ι ℝ) (p : ι) (x : ℝ) : Matrix ι ι ℝ :=
  fun i j => B i j + if i=p ∧ j=p then x else 0

def attached (B : Matrix ι ι ℝ) (p : ι) (r : κ → ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ
  | .inl i, .inl j => B i j
  | .inl i, .inr j => if i=p then r j else 0
  | .inr _, .inl j => if j=p then 1 else 0
  | .inr i, .inr j => if i=j then -1 else 0

omit [DecidableEq ι] in
theorem pencil_of_dStable {B : Matrix ι ι ℝ} (hB : DStable B)
    (q : ι → ℝ) (hq : ∀ i, 0<q i) (z : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (he : ∀ i, ∑ j, (B i j : ℂ)*v j = z*(q i : ℂ)*v i) : z.re < 0 := by
  let w : ι → ℂ := fun i => (q i : ℂ)*v i
  have hw : w ≠ 0 := by
    intro h
    apply hv
    funext i
    have hi := congrFun h i
    have hqi : (q i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hq i))
    exact (mul_eq_zero.mp hi).resolve_left hqi
  apply hB (fun i => (q i)⁻¹) (fun i => inv_pos.mpr (hq i)) z w
  refine ⟨hw, fun i => ?_⟩
  change (∑ j, ((B i j * (q j)⁻¹ : ℝ) : ℂ) * w j) = z * w i
  have hh : ∀ j, ((B i j * (q j)⁻¹ : ℝ) : ℂ) * w j = (B i j : ℂ)*v j := by
    intro j
    have hqj : (q j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hq j))
    dsimp [w]
    push_cast
    field_simp
  simp_rw [hh]
  simpa [w, mul_assoc] using he i

theorem lag_den_ne {z : ℂ} {t : ℝ} (hz : 0 ≤ z.re) (ht : 0<t) :
    1+z*(t : ℂ) ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp at hh
  nlinarith [mul_nonneg hz ht.le]

omit [DecidableEq κ] in
/-- Direct spectral safety, including the singular endpoint exception handled
by a literal trivial-kernel assumption at total load. -/
theorem pencil_safety [Nonempty κ] (B : Matrix ι ι ℝ) (p : ι) (r : κ → ℝ)
    (hr : ∀ j, 0<r j)
    (hs : ∀ x : ℝ, 0<x → x < ∑ j, r j → DStable (loadCore B p x))
    (q : ι → ℝ) (t : κ → ℝ) (hq : ∀ i, 0<q i) (ht : ∀ j, 0<t j)
    (z : ℂ) (v : ι → ℂ) (w : κ → ℂ)
    (hn : v ≠ 0 ∨ w ≠ 0)
    (hzero : z=0 → ∀ v : ι → ℂ,
      (∀ i, ∑ j, (loadCore B p (∑ k, r k) i j : ℂ)*v j = 0) → v=0)
    (hc : ∀ i, (∑ j, (B i j : ℂ)*v j) +
      (if i=p then ∑ j, (r j : ℂ)*w j else 0) = z*(q i : ℂ)*v i)
    (hl : ∀ j, v p-w j = z*(t j : ℂ)*w j) : z.re < 0 := by
  by_contra! hz
  have hw : ∀ j, w j = v p / (1+z*(t j : ℂ)) := by
    intro j
    apply (eq_div_iff (lag_den_ne hz (ht j))).mpr
    linear_combination -(hl j)
  have hv : v ≠ 0 := by
    intro h
    have hw0 : w=0 := by ext j; simp [hw j, h]
    exact hn.elim (fun h' => h' h) (fun h' => h' hw0)
  by_cases hz0 : z=0
  · apply hv
    apply hzero hz0
    intro i
    have hi := hc i
    simp only [hz0, zero_mul] at hi
    simp only [loadCore, Complex.ofReal_add, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero,
      add_mul, Finset.sum_add_distrib]
    by_cases hip : i=p
    · subst i
      simpa [hw, hz0, Finset.sum_mul] using hi
    · simpa [hip] using hi
  · let x : ℝ := ∑ j, staticLoad z (r j) (t j)
    let a : ℝ := ∑ j, lagShift z (r j) (t j)
    have hx : 0<x := Finset.sum_pos (fun j _ => (load_bounds hz hz0 (hr j) (ht j)).1)
      Finset.univ_nonempty
    have hxG : x < ∑ j, r j := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun j _ => (load_bounds hz hz0 (hr j) (ht j)).2)
    have ha : 0<a := Finset.sum_pos (fun j _ => shift_pos hz (hr j) (ht j))
      Finset.univ_nonempty
    let q' : ι → ℝ := fun i => q i + if i=p then a else 0
    have hq' : ∀ i, 0<q' i := by intro i; dsimp [q']; split_ifs <;> linarith [hq i]
    have hsum : (∑ j, (r j : ℂ)*w j) + z*(a : ℂ)*v p = (x : ℂ)*v p := by
      have hh : ∀ j, (r j : ℂ)*w j + z*(lagShift z (r j) (t j) : ℂ)*v p =
          (staticLoad z (r j) (t j) : ℂ)*v p := by
        intro j
        rw [hw j]
        have h := congrArg (fun k : ℂ => k*v p) (absorption (r := r j) hz (ht j))
        convert h using 1
        ring
      have h := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hh j)
      simpa [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, x, a] using h
    have he : ∀ i, ∑ j, (loadCore B p x i j : ℂ)*v j = z*(q' i : ℂ)*v i := by
      intro i
      have hi := hc i
      simp only [loadCore, Complex.ofReal_add, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_zero,
        add_mul, Finset.sum_add_distrib]
      by_cases hip : i=p
      · subst i
        simp only [ite_true] at hi
        simp [q']
        linear_combination hi - hsum
      · simpa [hip, q'] using hi
    exact (not_lt_of_ge hz) (pencil_of_dStable (hs x hx hxG) q' hq' z v hv he)

/-- End-to-end matrix theorem: static D-stability on the open load interval
and a trivial total-load kernel imply D-stability of every positive partition. -/
theorem attached_dStable [Nonempty κ] (B : Matrix ι ι ℝ) (p : ι) (r : κ → ℝ)
    (hr : ∀ j, 0<r j)
    (hs : ∀ x : ℝ, 0<x → x < ∑ j, r j → DStable (loadCore B p x))
    (hzero : ∀ v : ι → ℂ,
      (∀ i, ∑ j, (loadCore B p (∑ k, r k) i j : ℂ)*v j = 0) → v=0) :
    DStable (attached B p r) := by
  intro d hd z u hu
  let v : ι → ℂ := fun i => (d (.inl i) : ℂ)*u (.inl i)
  let w : κ → ℂ := fun j => (d (.inr j) : ℂ)*u (.inr j)
  have hdn (i : ι ⊕ κ) : (d i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd i))
  have hn : v ≠ 0 ∨ w ≠ 0 := by
    by_contra! h
    apply hu.1
    funext i
    cases i with
    | inl i => exact (mul_eq_zero.mp (congrFun h.1 i)).resolve_left (hdn (.inl i))
    | inr j => exact (mul_eq_zero.mp (congrFun h.2 j)).resolve_left (hdn (.inr j))
  apply pencil_safety B p r hr hs
    (fun i => (d (.inl i))⁻¹) (fun j => (d (.inr j))⁻¹)
    (fun i => inv_pos.mpr (hd (.inl i))) (fun j => inv_pos.mpr (hd (.inr j))) z v w hn (fun _ => hzero)
  · intro i
    have hi := hu.2 (.inl i)
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Fintype.sum_sum_type,
      attached, Complex.ofReal_mul] at hi
    have he : z*((d (.inl i))⁻¹ : ℝ)*v i = z*u (.inl i) := by
      dsimp [v]
      push_cast
      field_simp [hdn]
    rw [he]
    by_cases hip : i=p
    · simpa [hip, v, w, mul_assoc] using hi
    · simpa [hip, v, w, mul_assoc] using hi
  · intro j
    have hj := hu.2 (.inr j)
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Fintype.sum_sum_type,
      attached, Complex.ofReal_mul] at hj
    have he : z*((d (.inr j))⁻¹ : ℝ)*w j = z*u (.inr j) := by
      dsimp [w]
      push_cast
      field_simp [hdn]
    rw [he]
    simpa [v, w, mul_assoc, sub_eq_add_neg,
      apply_ite (fun x : ℝ => (x : ℂ))] using hj

/-- The singular endpoint still excludes every nonzero closed-half-plane eigenvalue. -/
theorem attached_nonzero_eigenvalue_neg [Nonempty κ]
    (B : Matrix ι ι ℝ) (p : ι) (r : κ → ℝ) (hr : ∀ j, 0<r j)
    (hs : ∀ x : ℝ, 0<x → x < ∑ j, r j → DStable (loadCore B p x))
    (d : ι ⊕ κ → ℝ) (hd : ∀ i, 0<d i) (z : ℂ) (u : ι ⊕ κ → ℂ)
    (hu : HasEigenpair (rightScale (attached B p r) d) z u) (hz : z≠0) : z.re<0 := by
  let v : ι → ℂ := fun i => (d (.inl i) : ℂ)*u (.inl i)
  let w : κ → ℂ := fun j => (d (.inr j) : ℂ)*u (.inr j)
  have hdn (i : ι ⊕ κ) : (d i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd i))
  have hn : v ≠ 0 ∨ w ≠ 0 := by
    by_contra! h
    apply hu.1
    funext i
    cases i with
    | inl i => exact (mul_eq_zero.mp (congrFun h.1 i)).resolve_left (hdn (.inl i))
    | inr j => exact (mul_eq_zero.mp (congrFun h.2 j)).resolve_left (hdn (.inr j))
  apply pencil_safety B p r hr hs
    (fun i => (d (.inl i))⁻¹) (fun j => (d (.inr j))⁻¹)
    (fun i => inv_pos.mpr (hd (.inl i))) (fun j => inv_pos.mpr (hd (.inr j))) z v w hn
    (fun hz0 => (hz hz0).elim)
  · intro i
    have hi := hu.2 (.inl i)
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Fintype.sum_sum_type,
      attached, Complex.ofReal_mul] at hi
    have he : z*((d (.inl i))⁻¹ : ℝ)*v i = z*u (.inl i) := by
      dsimp [v]
      push_cast
      field_simp [hdn]
    rw [he]
    by_cases hip : i=p
    · simpa [hip, v, w, mul_assoc] using hi
    · simpa [hip, v, w, mul_assoc] using hi
  · intro j
    have hj := hu.2 (.inr j)
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Fintype.sum_sum_type,
      attached, Complex.ofReal_mul] at hj
    have he : z*((d (.inr j))⁻¹ : ℝ)*w j = z*u (.inr j) := by
      dsimp [w]
      push_cast
      field_simp [hdn]
    rw [he]
    simpa [v, w, mul_assoc, sub_eq_add_neg,
      apply_ite (fun x : ℝ => (x : ℂ))] using hj

/-- The same spectral theorem with the ordinary real determinant endpoint test. -/
theorem attached_dStable_of_det [Nonempty κ] (B : Matrix ι ι ℝ) (p : ι) (r : κ → ℝ)
    (hr : ∀ j, 0<r j)
    (hs : ∀ x : ℝ, 0<x → x < ∑ j, r j → DStable (loadCore B p x))
    (hdet : (loadCore B p (∑ j, r j)).det ≠ 0) : DStable (attached B p r) := by
  apply attached_dStable B p r hr hs
  intro v hv
  let A := loadCore B p (∑ j, r j)
  have hc : (complexify A).det ≠ 0 := by
    have hmap := (Complex.ofRealHom.map_det A).symm
    change (Complex.ofRealHom.mapMatrix A).det ≠ 0
    rw [hmap]
    change (A.det : ℂ) ≠ 0
    exact_mod_cast (show A.det ≠ 0 from hdet)
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det (complexify A)).mpr (isUnit_iff_ne_zero.mpr hc))
  apply hi
  ext i
  simpa [Matrix.mulVec, dotProduct, complexify, A] using hv i

end
end DStabilityCharacterization.Granularity
