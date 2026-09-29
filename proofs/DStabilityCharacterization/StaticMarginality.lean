module

public import proofs.DStabilityCharacterization.Granularity

@[expose] public section

namespace DStabilityCharacterization.StaticMarginality
open DUnstableCores Granularity
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pencil (B : Matrix ι ι ℝ) (q : ι → ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  fun i j => (if i=j then z*(q i : ℂ) else 0) - (B i j : ℂ)

def diagAdd (M : Matrix ι ι ℂ) (p : ι) (a : ℂ) : Matrix ι ι ℂ :=
  M.updateRow p (M p + a • Pi.single p 1)

omit [Fintype ι] in
theorem diagAdd_apply (M : Matrix ι ι ℂ) (p : ι) (a : ℂ) (i j : ι) :
    diagAdd M p a i j = M i j + if i=p ∧ j=p then a else 0 := by
  change (Function.update (fun k l => M k l) p
    (fun l => M p l + a * (Pi.single p (1 : ℂ) : ι → ℂ) l) i) j = _
  by_cases hi : i=p <;> by_cases hj : j=p <;>
    simp [hi, hj]

theorem det_diagAdd (M : Matrix ι ι ℂ) (p : ι) (a : ℂ) :
    (diagAdd M p a).det = M.det + a*M.adjugate p p := by
  rw [diagAdd, Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_smul, Matrix.adjugate_apply]

theorem det_zero_iff_kernel (M : Matrix ι ι ℂ) :
    M.det=0 ↔ ∃ v : ι → ℂ, v ≠ 0 ∧ M.mulVec v = 0 := by
  constructor
  · intro h
    have hn : ¬ Function.Injective M.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      exact not_not_intro h
    obtain ⟨u,v,huv,hne⟩ := Function.not_injective_iff.mp hn
    refine ⟨u-v, sub_ne_zero.mpr hne, ?_⟩
    simp [Matrix.mulVec_sub, huv]
  · rintro ⟨v,hv,h⟩
    by_contra hd
    have hi := Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hd))
    exact hv (hi (by simpa using h))

theorem kernel_pencil_iff (B : Matrix ι ι ℝ) (q : ι → ℝ) (z : ℂ) (v : ι → ℂ) :
    (pencil B q z).mulVec v = 0 ↔
      ∀ i, ∑ j, (B i j : ℂ)*v j = z*(q i : ℂ)*v i := by
  simp only [funext_iff, Matrix.mulVec, dotProduct, pencil, sub_mul,
    Finset.sum_sub_distrib, Pi.zero_apply, sub_eq_zero]
  simp [ite_mul, eq_comm]

theorem pencil_det_ne (B : Matrix ι ι ℝ) (hB : DStable B)
    (q : ι → ℝ) (hq : ∀ i, 0<q i) (z : ℂ) (hz : 0≤z.re) :
    (pencil B q z).det ≠ 0 := by
  intro h
  obtain ⟨v,hv,he⟩ := (det_zero_iff_kernel _).mp h
  exact (not_lt_of_ge hz) (pencil_of_dStable hB q hq z v hv
    ((kernel_pencil_iff B q z v).mp he))

omit [Fintype ι] in
theorem pencil_load (B : Matrix ι ι ℝ) (p : ι) (x : ℝ) (q : ι → ℝ) (z : ℂ) :
    pencil (loadCore B p x) q z = diagAdd (pencil B q z) p (-x) := by
  ext i j
  simp only [pencil, loadCore, Complex.ofReal_add, diagAdd_apply]
  split_ifs <;> push_cast <;> ring

theorem pencil_cofactor_ne (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (x : ℝ) (q : ι → ℝ) (hq : ∀ i, 0<q i)
    (z : ℂ) (hz : 0≤z.re) (he : (pencil (loadCore B p x) q z).det=0) :
    (pencil B q z).adjugate p p ≠ 0 := by
  intro hc
  rw [pencil_load, det_diagAdd, hc, mul_zero, add_zero] at he
  exact pencil_det_ne B hB q hq z hz he

theorem dUnstable_of_pencil (B : Matrix ι ι ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0<q i) (z : ℂ) (hz : 0<z.re)
    (he : (pencil B q z).det=0) : DUnstable B := by
  obtain ⟨v,hv,he⟩ := (det_zero_iff_kernel _).mp he
  have he' := (kernel_pencil_iff B q z v).mp he
  let w : ι → ℂ := fun i => (q i : ℂ)*v i
  refine ⟨fun i => (q i)⁻¹, fun i => inv_pos.mpr (hq i), z, w, hz, ?_, ?_⟩
  · intro h
    apply hv
    funext i
    have hi := congrFun h i
    have hqi : (q i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hq i))
    exact (mul_eq_zero.mp hi).resolve_left hqi
  · intro i
    change (∑ j, ((B i j * (q j)⁻¹ : ℝ) : ℂ) * w j) = z * w i
    have hh : ∀ j, ((B i j * (q j)⁻¹ : ℝ) : ℂ) * w j = (B i j : ℂ)*v j := by
      intro j
      have hqj : (q j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hq j))
      dsimp [w]
      push_cast
      field_simp
    simp_rw [hh]
    simpa [w, mul_assoc] using he' i

def quotient (B : Matrix ι ι ℝ) (p : ι) (q : ι → ℝ) (z : ℂ) : ℂ :=
  (pencil B q z).det / (pencil B q z).adjugate p p

theorem quotient_at_contact (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (x : ℝ) (q : ι → ℝ) (hq : ∀ i, 0<q i)
    (z : ℂ) (hz : 0≤z.re) (he : (pencil (loadCore B p x) q z).det=0) :
    quotient B p q z = (x : ℂ) := by
  have hc := pencil_cofactor_ne B hB p x q hq z hz he
  rw [pencil_load, det_diagAdd] at he
  apply (div_eq_iff hc).mpr
  linear_combination he

omit [Fintype ι] in
theorem continuous_pencil (B : Matrix ι ι ℝ) (q : ι → ℝ) :
    Continuous (pencil B q) := by
  apply continuous_matrix
  intro i j
  dsimp [pencil]
  split_ifs <;> fun_prop

theorem continuousAt_quotient (B : Matrix ι ι ℝ) (p : ι) (q : ι → ℝ)
    (z : ℂ) (hc : (pencil B q z).adjugate p p ≠ 0) :
    ContinuousAt (quotient B p q) z := by
  apply ContinuousAt.div
  · exact (continuous_pencil B q).matrix_det.continuousAt
  · exact ((continuous_pencil B q).matrix_adjugate.matrix_elem p p).continuousAt
  · exact hc

theorem quotient_real (B : Matrix ι ι ℝ) (p : ι) (q : ι → ℝ) (s : ℝ) :
    (quotient B p q (s : ℂ)).im = 0 := by
  let M : Matrix ι ι ℝ := fun i j => (if i=j then s*q i else 0)-B i j
  have hp : pencil B q (s : ℂ) = Complex.ofRealHom.mapMatrix M := by
    ext i j
    change (if i = j then (s : ℂ) * (q i : ℂ) else 0) - (B i j : ℂ) =
      (((if i = j then s * q i else 0) - B i j : ℝ) : ℂ)
    split_ifs <;> simp
  unfold quotient
  rw [hp, ← Complex.ofRealHom.map_det, ← Complex.ofRealHom.map_adjugate]
  change ((M.det : ℂ) / (M.adjugate p p : ℂ)).im = 0
  rw [← Complex.ofReal_div]
  rfl

omit [Fintype ι] in
theorem pencil_corrected (B : Matrix ι ι ℝ) (p : ι) (q : ι → ℝ)
    (z : ℂ) (k y : ℝ) :
    pencil (loadCore B p y) (fun i => q i + if i=p then k else 0) z =
      diagAdd (pencil B q z) p (z*(k : ℂ)-(y : ℂ)) := by
  ext i j
  simp only [pencil, loadCore, diagAdd_apply, Complex.ofReal_add]
  by_cases hi : i=p
  · subst i
    by_cases hj : j=p
    · subst j
      simp
      ring
    · simp [hj, Ne.symm hj]
  · by_cases hij : i=j
    · subst j
      simp [hi]
    · simp [hi, hij]

theorem correction_identity (f : ℂ) (s w : ℝ) (h : w=0 → f.im=0) :
    f + ((s : ℂ)+(w : ℂ)*Complex.I)*(-f.im/w : ℝ) -
      (f.re+s*(-f.im/w) : ℝ) = 0 := by
  apply Complex.ext
  · simp
  · by_cases hw : w=0
    · simp [hw, h hw]
    · simp
      field_simp
      ring

/-- Every imaginary-axis contact at a positive coordinate load is approached
by literal strict-growth loads. The zero-frequency case is included. -/
theorem contact_nearby_growth (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (x : ℝ) (hx : 0<x) (q : ι → ℝ) (hq : ∀ i, 0<q i)
    (z : ℂ) (hz : z.re=0) (he : (pencil (loadCore B p x) q z).det=0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ y : ℝ, 0<y ∧ |y-x|<ε ∧ DUnstable (loadCore B p y) := by
  have hc := pencil_cofactor_ne B hB p x q hq z (by simp [hz]) he
  have hf0 := quotient_at_contact B hB p x q hq z (by simp [hz]) he
  let f : ℝ → ℂ := fun s => quotient B p q ((s : ℂ)+z)
  let k : ℝ → ℝ := fun s => -(f s).im/z.im
  let y : ℝ → ℝ := fun s => (f s).re+s*k s
  have hg : Continuous (fun s : ℝ => (s : ℂ)+z) := by fun_prop
  have hf : ContinuousAt f 0 :=
    (continuousAt_quotient B p q z hc).comp_of_eq
      (hg.continuousAt (x := 0)) (by simp)
  have hk : ContinuousAt k 0 := by
    exact (Complex.continuous_im.continuousAt.comp hf).neg.div_const z.im
  have hy : ContinuousAt y 0 := by
    exact (Complex.continuous_re.continuousAt.comp hf).add (continuousAt_id.mul hk)
  have hfzero : f 0 = (x : ℂ) := by simpa [f] using hf0
  have hkzero : k 0 = 0 := by simp [k, hfzero]
  have hyzero : y 0 = x := by simp [y, hfzero]
  have hco : ContinuousAt (fun s : ℝ => (pencil B q ((s : ℂ)+z)).adjugate p p) 0 := by
    exact (((continuous_pencil B q).matrix_adjugate.matrix_elem p p).comp hg).continuousAt
  have evc := hco.eventually_ne (by simpa using hc)
  have evq : ∀ᶠ s in nhds (0 : ℝ), 0<q p+k s :=
    continuousAt_const.eventually_lt (continuousAt_const.add hk) (by simpa [hkzero] using hq p)
  have evy : ∀ᶠ s in nhds (0 : ℝ), 0<y s :=
    continuousAt_const.eventually_lt hy (by simpa [hyzero] using hx)
  have eve : ∀ᶠ s in nhds (0 : ℝ), |y s-x|<ε :=
    (hy.sub continuousAt_const).abs.eventually_lt continuousAt_const (by simpa [hyzero] using hε)
  obtain ⟨a,ha,hball⟩ := Metric.eventually_nhds_iff.mp (evc.and (evq.and (evy.and eve)))
  let s : ℝ := a/2
  have hs : 0<s := by dsimp [s]; positivity
  have hsa : dist s 0<a := by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; dsimp [s]; linarith
  obtain ⟨hc',hq',hy',he'⟩ := hball hsa
  refine ⟨y s,hy',he',?_⟩
  apply dUnstable_of_pencil (loadCore B p (y s))
    (fun i => q i + if i=p then k s else 0)
    (fun i => by
      by_cases hi : i=p
      · simpa [hi] using hq'
      · simpa [hi] using hq i)
    ((s : ℂ)+z) (by simpa [hz] using hs)
  rw [pencil_corrected, det_diagAdd]
  have hdiv : (pencil B q ((s : ℂ)+z)).det = f s *
      (pencil B q ((s : ℂ)+z)).adjugate p p := by
    exact (div_eq_iff hc').mp rfl
  rw [hdiv, ← add_mul]
  have hzrep : z = (z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
  have halg := correction_identity (f s) s z.im (by
    intro hi
    have hz0 : z=0 := Complex.ext hz hi
    simpa [f,hz0] using quotient_real B p q s)
  have hzero : f s + (((s : ℂ)+z)*(k s : ℂ)-(y s : ℂ))=0 := by
    rw [hzrep]
    simpa [k,y,sub_eq_add_neg,add_assoc] using halg
  rw [hzero, zero_mul]

theorem pencil_det_of_scaled_eigenpair (B : Matrix ι ι ℝ) (d : ι → ℝ)
    (hd : ∀ i, 0<d i) (z : ℂ) (u : ι → ℂ)
    (hu : HasEigenpair (rightScale B d) z u) :
    (pencil B (fun i => (d i)⁻¹) z).det=0 := by
  let v : ι → ℂ := fun i => (d i : ℂ)*u i
  have hdn (i : ι) : (d i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd i))
  apply (det_zero_iff_kernel _).mpr
  refine ⟨v, ?_, (kernel_pencil_iff _ _ _ _).mpr ?_⟩
  · intro h
    apply hu.1
    funext i
    exact (mul_eq_zero.mp (congrFun h i)).resolve_left (hdn i)
  · intro i
    have hi := hu.2 i
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Complex.ofReal_mul] at hi
    calc
      (∑ j, (B i j : ℂ)*v j) = ∑ j, ((B i j : ℂ)*(d j : ℂ))*u j := by
        apply Finset.sum_congr rfl
        intro j _
        simp [v, mul_assoc]
      _ = z*u i := hi
      _ = z*((d i)⁻¹ : ℝ)*v i := by
        dsimp [v]
        push_cast
        field_simp [hdn]

/-- On a coordinate-load interval with no strict growth, every point before
its upper endpoint is strictly D-stable. In particular this closes the
static marginality implication needed by the first-growth infimum. -/
theorem stable_of_no_growth_before (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (L : ℝ)
    (hng : ∀ y : ℝ, 0<y → y<L → ¬ DUnstable (loadCore B p y))
    (x : ℝ) (hx : 0≤x) (hxL : x<L) : DStable (loadCore B p x) := by
  by_cases hx0 : x=0
  · have heq : loadCore B p x = B := by ext i j; simp [loadCore, hx0]
    simpa [heq] using hB
  have hxpos : 0<x := lt_of_le_of_ne hx (Ne.symm hx0)
  intro d hd z u hu
  by_contra! hz
  by_cases hzpos : 0<z.re
  · exact hng x hxpos hxL ⟨d,hd,z,u,hzpos,hu⟩
  · have hz0 : z.re=0 := le_antisymm (le_of_not_gt hzpos) hz
    have he := pencil_det_of_scaled_eigenpair (loadCore B p x) d hd z u hu
    obtain ⟨y,hy,hclose,hgrow⟩ := contact_nearby_growth B hB p x hxpos
      (fun i => (d i)⁻¹) (fun i => inv_pos.mpr (hd i)) z hz0 he (L-x) (sub_pos.mpr hxL)
    exact hng y hy (by have hh := le_abs_self (y-x); linarith) hgrow

end
end DStabilityCharacterization.StaticMarginality
