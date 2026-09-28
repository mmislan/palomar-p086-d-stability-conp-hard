module

public import proofs.DStabilityCharacterization.StaticMarginality
public import proofs.DStabilityCharacterization.FiniteRealization
public import proofs.DStabilityCharacterization.DiagonalGrowth
public import proofs.DStabilityCharacterization.ZeroEndpoint

@[expose] public section

/-! Full coordinate-port granularity threshold, in literal matrix spectral semantics. -/
namespace DStabilityCharacterization.Granularity
open DUnstableCores
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def growthLoads (B : Matrix ι ι ℝ) (p : ι) : Set ℝ :=
  {x | 0≤x ∧ DUnstable (loadCore B p x)}

def threshold (B : Matrix ι ι ℝ) (p : ι) : ℝ := sInf (growthLoads B p)

theorem growthLoads_nonempty (B : Matrix ι ι ℝ) (p : ι) :
    (growthLoads B p).Nonempty := growth_loads_nonempty B p

theorem growthLoads_bddBelow (B : Matrix ι ι ℝ) (p : ι) :
    BddBelow (growthLoads B p) := ⟨0,fun _ h => h.1⟩

theorem threshold_nonneg (B : Matrix ι ι ℝ) (p : ι) : 0≤threshold B p :=
  le_csInf (growthLoads_nonempty B p) (fun _ h => h.1)

theorem threshold_le_diagonal (B : Matrix ι ι ℝ) (hB : DStable B) (p : ι) :
    threshold B p ≤ -B p p := by
  by_contra! h
  let x := (-B p p+threshold B p)/2
  have hd := diagonal_nonpos_of_dStable B hB p
  have hn := threshold_nonneg B p
  have hx : 0≤x := by dsimp [x]; linarith
  have hg := load_unstable_above_diagonal B p x (by dsimp [x]; linarith)
  have hi : threshold B p≤x := csInf_le (growthLoads_bddBelow B p) ⟨hx,hg⟩
  dsimp [x] at hi
  linarith

theorem static_stable_below_threshold (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (x : ℝ) (hx : 0≤x) (hxt : x<threshold B p) :
    DStable (loadCore B p x) := by
  apply StaticMarginality.stable_of_no_growth_before B hB p (threshold B p) ?_ x hx hxt
  intro y hy hyt hun
  have hh : threshold B p≤y := csInf_le (growthLoads_bddBelow B p) ⟨hy.le,hun⟩
  linarith

theorem det_ne_zero_of_dStable (B : Matrix ι ι ℝ) (hB : DStable B) : B.det≠0 := by
  intro hdet
  obtain ⟨v,hv,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨u,hu⟩ := scaled_zero_of_kernel B v hv hker (fun _ => 1) (by simp)
  have hh := hB (fun _ => 1) (by simp) 0 u hu
  norm_num at hh

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

theorem below_threshold_dStable (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (r : κ → ℝ) (hr : ∀ j, 0<r j)
    (hG : (∑ j, r j)<threshold B p) : DStable (attached B p r) := by
  apply attached_dStable_of_det B p r hr
  · intro x hx hxG
    exact static_stable_below_threshold B hB p x hx.le (hxG.trans hG)
  · apply det_ne_zero_of_dStable
    apply static_stable_below_threshold B hB p _ _ hG
    exact Finset.sum_nonneg (fun j _ => (hr j).le)

theorem at_threshold_dStable_iff (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (r : κ → ℝ) (hr : ∀ j, 0<r j)
    (hG : (∑ j, r j)=threshold B p) :
    DStable (attached B p r) ↔ (loadCore B p (threshold B p)).det≠0 := by
  constructor
  · intro ha hz
    apply attached_not_dStable_of_det_zero B p r _ ha
    simpa [hG] using hz
  · intro hz
    apply attached_dStable_of_det B p r hr
    · intro x hx hxG
      exact static_stable_below_threshold B hB p x hx.le (by simpa [hG] using hxG)
    · simpa [hG] using hz

theorem at_threshold_nonzero_eigenvalue_neg (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (r : κ → ℝ) (hr : ∀ j, 0<r j)
    (hG : (∑ j, r j)=threshold B p)
    (d : ι ⊕ κ → ℝ) (hd : ∀ i, 0<d i) (z : ℂ) (u : ι ⊕ κ → ℂ)
    (hu : HasEigenpair (rightScale (attached B p r) d) z u) (hz : z≠0) : z.re<0 := by
  apply attached_nonzero_eigenvalue_neg B p r hr ?_ d hd z u hu hz
  intro x hx hxG
  exact static_stable_below_threshold B hB p x hx.le (by simpa [hG] using hxG)

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
theorem above_threshold_fine_unstable (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (G : ℝ) (hG : threshold B p<G) :
    ∃ ε : ℝ, 0<ε ∧ ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (r : κ → ℝ),
      (∀ j, 0<r j) → (∑ j, r j)=G → (∀ j, r j<ε) → DUnstable (attached B p r) := by
  obtain ⟨x,hx,hxG⟩ := exists_lt_of_csInf_lt (growthLoads_nonempty B p) hG
  have hx0 : x≠0 := by
    intro h
    have hh : loadCore B p x=B := by ext i j; simp [loadCore,h]
    rcases hx.2 with ⟨d,hd,z,v,hz,hv⟩
    rw [hh] at hv
    have hn := hB d hd z v hv
    linarith
  exact sufficiently_fine_unstable B p G x (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hxG hx.2

/-- Complete threshold classification for an arbitrary finite positive partition.
The last clause's tolerance additionally ranges over every finite leaf type. -/
theorem granularity_threshold (B : Matrix ι ι ℝ) (hB : DStable B)
    (p : ι) (r : κ → ℝ) (hr : ∀ j, 0<r j) :
    (0≤threshold B p ∧ threshold B p≤-B p p) ∧
    ((∑ j, r j)<threshold B p → DStable (attached B p r)) ∧
    ((∑ j, r j)=threshold B p →
      (DStable (attached B p r) ↔ (loadCore B p (threshold B p)).det≠0) ∧
      (∀ d : ι ⊕ κ → ℝ, (∀ i, 0<d i) → ∀ z u,
        HasEigenpair (rightScale (attached B p r) d) z u → z≠0 → z.re<0) ∧
      ((loadCore B p (threshold B p)).det=0 →
        ∀ d : ι ⊕ κ → ℝ, (∀ i, 0<d i) →
          ∃ u, HasEigenpair (rightScale (attached B p r) d) 0 u)) ∧
    (∀ G : ℝ, threshold B p<G →
      ∃ ε : ℝ, 0<ε ∧ ∀ {κ' : Type*} [Fintype κ'] [DecidableEq κ'] (r' : κ' → ℝ),
        (∀ j, 0<r' j) → (∑ j, r' j)=G → (∀ j, r' j<ε) → DUnstable (attached B p r')) := by
  refine ⟨⟨threshold_nonneg B p, threshold_le_diagonal B hB p⟩,
    below_threshold_dStable B hB p r hr, ?_, above_threshold_fine_unstable B hB p⟩
  intro hG
  refine ⟨at_threshold_dStable_iff B hB p r hr hG,
    at_threshold_nonzero_eigenvalue_neg B hB p r hr hG, ?_⟩
  intro hz d hd
  apply attached_zero_eigenpair_of_det_zero B p r _ d hd
  simpa [hG] using hz

end
end DStabilityCharacterization.Granularity
