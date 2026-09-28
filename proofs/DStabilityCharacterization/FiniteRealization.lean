module

public import proofs.DStabilityCharacterization.Granularity

@[expose] public section

namespace DStabilityCharacterization.Granularity
open DUnstableCores
open scoped BigOperators
noncomputable section

theorem crossing_subset {κ : Type*} [DecidableEq κ] (s : Finset κ)
    (r : κ → ℝ) (X ε : ℝ) (hX : 0 ≤ X)
    (hr : ∀ j ∈ s, r j < ε) (hS : X < ∑ j ∈ s, r j) :
    ∃ a ⊆ s, X < ∑ j ∈ a, r j ∧ (∑ j ∈ a, r j) < X+ε := by
  induction s using Finset.induction_on with
  | empty => simp at hS; linarith
  | @insert j s hj ih =>
    by_cases hs : X < ∑ k ∈ s, r k
    · obtain ⟨a, ha, hx, he⟩ := ih (fun k hk => hr k (Finset.mem_insert_of_mem hk)) hs
      exact ⟨a, ha.trans (Finset.subset_insert _ _), hx, he⟩
    · refine ⟨insert j s, Finset.Subset.refl _, hS, ?_⟩
      rw [Finset.sum_insert hj]
      have := hr j (Finset.mem_insert_self j s)
      linarith

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem lag_surjective (z : ℂ) (hz : 0<z.re) (y : ℝ) (hy : 0<y) (hy1 : y<1) :
    ∃ t : ℝ, 0<t ∧ staticLoad z 1 t = y := by
  let k := z.re^2+z.im^2
  have hk : 0<k := by dsimp [k]; nlinarith [sq_nonneg z.im]
  let c := z.re*(1-y)
  let d := c^2+k*y*(1-y)
  have hc : 0<c := mul_pos hz (sub_pos.mpr hy1)
  have hd : 0≤d := by dsimp [d]; positivity
  have hroot := Real.sq_sqrt hd
  have hsqrt := Real.sqrt_nonneg d
  let t := (c+Real.sqrt d)/(k*y)
  have ht : 0<t := div_pos (by positivity) (mul_pos hk hy)
  refine ⟨t, ht, ?_⟩
  have ht' : t*(k*y)=c+Real.sqrt d := div_mul_cancel₀ _ (ne_of_gt (mul_pos hk hy))
  have heq : k*y*t^2 - 2*c*t = 1-y := by
    have hh : (t*(k*y)-c)^2=d := by rw [ht']; simpa using hroot
    dsimp [d] at hh
    have hcancel : k*y*(k*y*t^2-2*c*t-(1-y))=0 := by nlinarith [hh]
    have hh0 := (mul_eq_zero.mp hcancel).resolve_left (ne_of_gt (mul_pos hk hy))
    linarith
  rw [staticLoad, div_eq_iff (ne_of_gt (denom_pos hz.le ht))]
  dsimp [denom, c, k] at *
  nlinarith

theorem small_delta (z : ℂ) (hz : 0<z.re) (G X q : ℝ)
    (hG : 0<G) (hXG : X<G) (hq : 0<q) :
    ∃ δ : ℝ, 0<δ ∧
      G*δ+G*(z.re^2+z.im^2)*δ^2/(2*z.re)<q ∧
      G*(z.re^2+z.im^2)*δ^2<G-X := by
  let k := z.re^2+z.im^2
  have hk : 0<k := by dsimp [k]; nlinarith [sq_nonneg z.im]
  let C := G+G*k/(2*z.re)
  have hC : 0<C := by dsimp [C]; positivity
  obtain ⟨δ, hd, hd'⟩ := exists_between
    (show 0 < min 1 (min (q/C) ((G-X)/(G*k))) by positivity)
  have hd1 : δ<1 := (lt_min_iff.mp hd').1
  have hdq : δ<q/C := (lt_min_iff.mp (lt_min_iff.mp hd').2).1
  have hdG : δ<(G-X)/(G*k) := (lt_min_iff.mp (lt_min_iff.mp hd').2).2
  have hd2 : δ^2≤δ := by nlinarith
  have hq' : δ*C<q := (lt_div_iff₀ hC).mp hdq
  have hG' : δ*(G*k)<G-X := (lt_div_iff₀ (mul_pos hG hk)).mp hdG
  have ha : G*k/(2*z.re)≥0 := by positivity
  have he : G*δ+G*k*δ^2/(2*z.re)≤δ*C := by
    dsimp [C]
    rw [show G*k*δ^2/(2*z.re)=(G*k/(2*z.re))*δ^2 by ring]
    nlinarith [mul_le_mul_of_nonneg_left hd2 ha]
  refine ⟨δ, hd, lt_of_le_of_lt he hq', ?_⟩
  exact lt_of_le_of_lt (by nlinarith [mul_le_mul_of_nonneg_left hd2 (mul_pos hG hk).le]) hG'

theorem load_linear (z : ℂ) (r t : ℝ) : staticLoad z r t = r*staticLoad z 1 t := by
  unfold staticLoad
  ring

theorem shift_le_time (z : ℂ) (hz : 0≤z.re) (r t : ℝ) (hr : 0≤r) (ht : 0<t) :
    lagShift z r t ≤ r*t := by
  have hd := denom_pos hz ht
  rw [lagShift, div_le_iff₀ hd]
  have h1 : 1≤denom z t := by unfold denom; nlinarith [mul_nonneg hz ht.le, sq_nonneg (z.im*t)]
  nlinarith [mul_nonneg hr ht.le, mul_le_mul_of_nonneg_left h1 (mul_nonneg hr ht.le)]

theorem shift_le_load (z : ℂ) (hz : 0<z.re) (r t : ℝ) (hr : 0≤r) (ht : 0<t) :
    lagShift z r t ≤ staticLoad z r t/(2*z.re) := by
  have hd := denom_pos hz.le ht
  rw [le_div_iff₀ (by positivity : 0<2*z.re)]
  rw [lagShift, staticLoad]
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hd).mpr
  nlinarith

theorem load_deficit_bound (z : ℂ) (hz : 0≤z.re) (t : ℝ) (ht : 0<t) :
    1-staticLoad z 1 t ≤ (z.re^2+z.im^2)*t^2 := by
  have hd := denom_pos hz ht
  have h1 : 1≤denom z t := by unfold denom; nlinarith [mul_nonneg hz ht.le, sq_nonneg (z.im*t)]
  have hk : 0≤(z.re^2+z.im^2)*t^2 := by positivity
  have he : 1-staticLoad z 1 t = (z.re^2+z.im^2)*t^2/denom z t := by
    unfold staticLoad
    field_simp
    unfold denom
    ring
  rw [he, div_le_iff₀ hd]
  nlinarith [mul_le_mul_of_nonneg_left h1 hk]

theorem sum_two_values (a : Finset κ) (r : κ → ℝ) (u v : ℝ) :
    (∑ j, r j*(if j∈a then u else v)) =
      (∑ j∈a, r j)*u + ((∑ j, r j)-(∑ j∈a, r j))*v := by
  have hs := Finset.sum_add_sum_compl a r
  rw [← Finset.sum_add_sum_compl a (fun j => r j*(if j∈a then u else v))]
  have h1 : (∑ j∈a, r j*(if j∈a then u else v))=(∑ j∈a, r j)*u := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    simp [hj]
  have h2 : (∑ j∈aᶜ, r j*(if j∈a then u else v))=(∑ j∈aᶜ, r j)*v := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_compl.mp hj]
  rw [h1, h2]
  have he : (∑ j∈aᶜ, r j)=(∑ j, r j)-(∑ j∈a, r j) := by linarith
  rw [he]

theorem partition_realization (z : ℂ) (hz : 0<z.re) (G X q : ℝ)
    (hX : 0<X) (hXG : X<G) (hq : 0<q) :
    ∃ ε : ℝ, 0<ε ∧ ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (r : κ → ℝ), (∀ j, 0<r j) →
      (∑ j, r j)=G → (∀ j, r j<ε) →
      ∃ t : κ → ℝ, (∀ j, 0<t j) ∧
        (∑ j, staticLoad z (r j) (t j))=X ∧
        (∑ j, lagShift z (r j) (t j))<q := by
  have hG : 0<G := lt_trans hX hXG
  obtain ⟨δ, hd, hdq, hdG⟩ := small_delta z hz G X q hG hXG hq
  let f := staticLoad z 1 δ
  have hz0 : z≠0 := by intro h; simp [h] at hz
  have hf := load_bounds hz.le hz0 (by norm_num : (0:ℝ)<1) hd
  change 0<f ∧ f<1 at hf
  have hdf : 0<1-f := sub_pos.mpr hf.2
  have hgap : 0<G-X := sub_pos.mpr hXG
  obtain ⟨ε, he, he'⟩ := exists_between
    (show 0 < min (G-X) (X*(1-f)) by positivity)
  refine ⟨ε, he, ?_⟩
  intro κ _ _ r hr hrG hre
  obtain ⟨a, _, haX, haε⟩ := crossing_subset Finset.univ r X ε hX.le
    (fun j _ => hre j) (by simpa [hrG] using hXG)
  let S := ∑ j∈a, r j
  change X<S at haX
  change S<X+ε at haε
  have heG := (lt_min_iff.mp he').1
  have heX := (lt_min_iff.mp he').2
  have hSG : S<G := by linarith
  have hS : 0<S := lt_trans hX haX
  have hdef := load_deficit_bound z hz.le δ hd
  change 1-f ≤ (z.re^2+z.im^2)*δ^2 at hdef
  have hN : 0<X-S*f := by nlinarith
  have hN1 : X-S*f<G-S := by
    have hgdef := mul_le_mul_of_nonneg_left hdef hG.le
    nlinarith [mul_lt_mul_of_pos_right hSG (sub_pos.mpr hf.2)]
  let y := (X-S*f)/(G-S)
  have hy : 0<y := div_pos hN (sub_pos.mpr hSG)
  have hy1 : y<1 := (div_lt_one (sub_pos.mpr hSG)).mpr hN1
  obtain ⟨T, hT, hTy⟩ := lag_surjective z hz y hy hy1
  let t : κ → ℝ := fun j => if j∈a then δ else T
  have ht : ∀ j, 0<t j := by intro j; dsimp [t]; split_ifs <;> assumption
  have hload : (∑ j, staticLoad z (r j) (t j))=S*f+(G-S)*y := by
    rw [show (∑ j, staticLoad z (r j) (t j)) = ∑ j, r j*staticLoad z 1 (t j) by
      apply Finset.sum_congr rfl
      intro j _
      exact load_linear z (r j) (t j)]
    have heq : ∀ j, staticLoad z 1 (t j) = if j∈a then f else y := by
      intro j
      dsimp [t]
      split_ifs <;> simp_all [f]
    simp_rw [heq]
    simpa [S, hrG] using sum_two_values a r f y
  have hNy : (G-S)*y=X-S*f := mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr hSG))
  refine ⟨t, ht, by rw [hload, hNy]; ring, ?_⟩
  have hshift : (∑ j, lagShift z (r j) (t j)) ≤ S*δ+(G-S)*(y/(2*z.re)) := by
    calc
      _ ≤ ∑ j, r j*(if j∈a then δ else y/(2*z.re)) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j∈a
        · simpa [t, hj] using shift_le_time z hz.le (r j) δ (hr j).le hd
        · have hl := shift_le_load z hz (r j) T (hr j).le hT
          rw [load_linear z (r j) T, hTy] at hl
          simpa [t, hj, mul_div_assoc] using hl
      _ = _ := by simpa [S, hrG] using sum_two_values a r δ (y/(2*z.re))
  have hNbound : X-S*f ≤ G*(z.re^2+z.im^2)*δ^2 := by
    have hh := mul_le_mul_of_nonneg_left hdef hG.le
    nlinarith
  have hslow : (G-S)*(y/(2*z.re)) ≤ G*(z.re^2+z.im^2)*δ^2/(2*z.re) := by
    rw [← mul_div_assoc, hNy]
    exact div_le_div_of_nonneg_right hNbound (by positivity)
  have hfast : S*δ≤G*δ := mul_le_mul_of_nonneg_right hSG.le hd.le
  linarith

omit [DecidableEq ι] in
theorem pencil_unstable (A : Matrix ι ι ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0<q i) (z : ℂ) (hz : 0<z.re) (v : ι → ℂ) (hv : v≠0)
    (he : ∀ i, ∑ j, (A i j : ℂ)*v j = z*(q i : ℂ)*v i) : DUnstable A := by
  let w : ι → ℂ := fun i => (q i : ℂ)*v i
  refine ⟨fun i => (q i)⁻¹, fun i => inv_pos.mpr (hq i), z, w, hz, ?_, ?_⟩
  · intro h
    apply hv
    funext i
    have hi := congrFun h i
    have hqi : (q i : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hq i))
    exact (mul_eq_zero.mp hi).resolve_left hqi
  · intro i
    change (∑ j, ((A i j * (q j)⁻¹ : ℝ) : ℂ) * w j) = z * w i
    have hh : ∀ j, ((A i j * (q j)⁻¹ : ℝ) : ℂ) * w j = (A i j : ℂ)*v j := by
      intro j
      have hqj : (q j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hq j))
      dsimp [w]
      push_cast
      field_simp
    simp_rw [hh]
    simpa [w, mul_assoc] using he i

theorem reverse_absorption (B : Matrix ι ι ℝ) (p : ι) (r t : κ → ℝ)
    (ht : ∀ j, 0<t j) (q : ι → ℝ) (hq : ∀ i, 0<q i)
    (z : ℂ) (hz : 0<z.re) (X : ℝ) (v : ι → ℂ) (hv : v≠0)
    (he : ∀ i, ∑ j, (loadCore B p X i j : ℂ)*v j = z*(q i : ℂ)*v i)
    (hload : ∑ j, staticLoad z (r j) (t j) = X)
    (hshift : ∑ j, lagShift z (r j) (t j) < q p) :
    DUnstable (attached B p r) := by
  let a : ℝ := ∑ j, lagShift z (r j) (t j)
  let q' : ι ⊕ κ → ℝ := Sum.elim (fun i => q i - if i=p then a else 0) t
  let w : κ → ℂ := fun j => v p/(1+z*(t j : ℂ))
  let u : ι ⊕ κ → ℂ := Sum.elim v w
  have hq' : ∀ i, 0<q' i := by
    intro i
    cases i with
    | inl i =>
      dsimp [q']
      split_ifs with hip
      · subst i; exact sub_pos.mpr hshift
      · simpa using hq i
    | inr j => exact ht j
  apply pencil_unstable (attached B p r) q' hq' z hz u
  · intro h
    apply hv
    funext i
    exact congrFun h (.inl i)
  · intro i
    cases i with
    | inl i =>
      have hi := he i
      simp only [loadCore, Complex.ofReal_add, apply_ite (fun x : ℝ => (x : ℂ)),
        Complex.ofReal_zero, add_mul, Finset.sum_add_distrib] at hi
      change (∑ j, (attached B p r (.inl i) j : ℂ)*u j) = _
      rw [Fintype.sum_sum_type]
      by_cases hip : i=p
      · subst i
        have hh : ∀ j, (r j : ℂ)*w j + z*(lagShift z (r j) (t j) : ℂ)*v p =
            (staticLoad z (r j) (t j) : ℂ)*v p := by
          intro j
          have h := congrArg (fun k : ℂ => k*v p) (absorption (r := r j) hz.le (ht j))
          convert h using 1
          dsimp [w]
          ring
        have hs := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hh j)
        have hsum : (∑ j, (r j : ℂ)*w j) + z*(a : ℂ)*v p = (X : ℂ)*v p := by
          rw [← hload]
          simpa [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, a] using hs
        simp only [attached, if_true, u, Sum.elim_inl, Sum.elim_inr]
        simp at hi
        dsimp [q']
        push_cast
        simp only [ite_true]
        linear_combination hi + hsum
      · simpa [attached, u, q', hip] using hi
    | inr j =>
      change (∑ k, (attached B p r (.inr j) k : ℂ)*u k) = _
      rw [Fintype.sum_sum_type]
      have hd := lag_den_ne hz.le (ht j)
      have hw : w j*(1+z*(t j : ℂ)) = v p := by dsimp [w]; exact div_mul_cancel₀ _ hd
      simp [attached, u, q', apply_ite (fun x : ℝ => (x : ℂ))]
      linear_combination -hw

/-- A strictly unstable static load is realized, with the same eigenvalue,
by every sufficiently fine finite positive partition. The tolerance is uniform
over the leaf type and its cardinality. -/
theorem sufficiently_fine_unstable (B : Matrix ι ι ℝ) (p : ι) (G X : ℝ)
    (hX : 0<X) (hXG : X<G) (hun : DUnstable (loadCore B p X)) :
    ∃ ε : ℝ, 0<ε ∧ ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (r : κ → ℝ),
      (∀ j, 0<r j) → (∑ j, r j)=G → (∀ j, r j<ε) →
      DUnstable (attached B p r) := by
  rcases hun with ⟨d, hd, z, u, hz, hu⟩
  let q : ι → ℝ := fun i => (d i)⁻¹
  let v : ι → ℂ := fun i => (d i : ℂ)*u i
  have hdn (i : ι) : (d i : ℂ)≠0 := by exact_mod_cast (ne_of_gt (hd i))
  have hq : ∀ i, 0<q i := fun i => inv_pos.mpr (hd i)
  have hv : v≠0 := by
    intro h
    apply hu.1
    funext i
    exact (mul_eq_zero.mp (congrFun h i)).resolve_left (hdn i)
  have he : ∀ i, ∑ j, (loadCore B p X i j : ℂ)*v j = z*(q i : ℂ)*v i := by
    intro i
    have hi := hu.2 i
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, Complex.ofReal_mul] at hi
    have heq : z*(q i : ℂ)*v i=z*u i := by
      dsimp [q, v]
      push_cast
      field_simp [hdn i]
    rw [heq]
    simpa [v, mul_assoc] using hi
  obtain ⟨ε, hε, hreal⟩ := partition_realization z hz G X (q p) hX hXG (hq p)
  refine ⟨ε, hε, ?_⟩
  intro κ _ _ r hr hrG hre
  obtain ⟨t, ht, hload, hshift⟩ := hreal r hr hrG hre
  exact reverse_absorption B p r t ht q hq z hz X v hv he hload hshift

end
end DStabilityCharacterization.Granularity
