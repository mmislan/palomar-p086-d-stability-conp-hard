module

public import proofs.DStabilityCharacterization.Granularity

@[expose] public section

namespace DStabilityCharacterization.Granularity
open DUnstableCores
open scoped BigOperators
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
theorem scaled_zero_of_kernel (A : Matrix ι ι ℝ) (y : ι → ℝ)
    (hy : y≠0) (he : A.mulVec y=0) (d : ι → ℝ) (hd : ∀ i, 0<d i) :
    ∃ u : ι → ℂ, HasEigenpair (rightScale A d) 0 u := by
  let u : ι → ℂ := fun i => (y i / d i : ℝ)
  refine ⟨u, ?_, ?_⟩
  · intro hu
    apply hy
    funext i
    have hi := congrFun hu i
    have hdi := ne_of_gt (hd i)
    dsimp [u] at hi
    have hr : y i / d i=0 := by exact_mod_cast hi
    exact (div_eq_zero_iff.mp hr).resolve_right hdi
  · intro i
    change (∑ j, ((A i j*d j : ℝ) : ℂ)*u j)=0*u i
    have hj : ∀ j, ((A i j*d j : ℝ) : ℂ)*u j = (A i j*y j : ℝ) := by
      intro j
      dsimp [u]
      have hdi : (d j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd j))
      push_cast
      field_simp
    simp_rw [hj]
    simp only [zero_mul]
    have hi := congrFun he i
    exact_mod_cast hi

theorem attached_zero_eigenpair_of_det_zero (B : Matrix ι ι ℝ) (p : ι) (r : κ → ℝ)
    (hz : (loadCore B p (∑ j, r j)).det=0)
    (d : ι ⊕ κ → ℝ) (hd : ∀ i, 0<d i) :
    ∃ u : ι ⊕ κ → ℂ, HasEigenpair (rightScale (attached B p r) d) 0 u := by
  obtain ⟨v,hv,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  let y : ι ⊕ κ → ℝ := Sum.elim v (fun _ => v p)
  have hy : y≠0 := by
    intro h
    apply hv
    funext i
    exact congrFun h (.inl i)
  apply scaled_zero_of_kernel (attached B p r) y hy ?_ d hd
  ext i
  cases i with
  | inl i =>
    have hi := congrFun hker i
    simp only [Matrix.mulVec, dotProduct, loadCore, add_mul, Finset.sum_add_distrib] at hi
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, attached, y, Sum.elim_inl,
      Sum.elim_inr, Pi.zero_apply]
    by_cases hip : i=p
    · subst i
      simpa [Finset.sum_mul] using hi
    · simpa [hip] using hi
  | inr j =>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, attached, y]

theorem attached_not_dStable_of_det_zero (B : Matrix ι ι ℝ) (p : ι) (r : κ → ℝ)
    (hz : (loadCore B p (∑ j, r j)).det=0) : ¬DStable (attached B p r) := by
  intro h
  obtain ⟨u,hu⟩ := attached_zero_eigenpair_of_det_zero B p r hz (fun _ => 1) (by simp)
  have hh := h (fun _ => 1) (by simp) 0 u hu
  norm_num at hh

end
end DStabilityCharacterization.Granularity
