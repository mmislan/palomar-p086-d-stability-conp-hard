module

public import proofs.DStabilityCharacterization.Granularity
public import proofs.DUnstableCores.RouthHurwitzDim3

@[expose] public section

namespace DStabilityCharacterization.Granularity
open DUnstableCores
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unstable_of_trace_pos (A : Matrix ι ι ℝ) (htr : 0<A.trace) :
    HurwitzUnstable A := by
  by_contra hn
  have hall : ∀ z ∈ (complexify A).charpoly.roots, z.re ≤ 0 := by
    intro z hz
    have hr := (Polynomial.mem_roots (Matrix.charpoly_monic (complexify A)).ne_zero).mp hz
    obtain ⟨v,hv⟩ := hasEigenpair_of_isRoot_complexified_charpoly hr
    by_contra! h
    exact hn ⟨z,v,h,hv⟩
  have hsum := Multiset.sum_map_le_sum_map Complex.re (fun _ : ℂ => (0:ℝ)) hall
  have he := congrArg Complex.re (Matrix.trace_eq_sum_roots_charpoly (complexify A))
  have hre : (complexify A).trace.re = A.trace := by
    simp [Matrix.trace, complexify]
  rw [hre] at he
  have hmap : ((complexify A).charpoly.roots.sum).re =
      ((complexify A).charpoly.roots.map Complex.re).sum := by
    exact map_multiset_sum Complex.reAddGroupHom _
  rw [hmap] at he
  simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_zero] at hsum
  linarith

theorem load_trace (B : Matrix ι ι ℝ) (p : ι) (x : ℝ) :
    (loadCore B p x).trace = B.trace+x := by
  simp [Matrix.trace, loadCore, Finset.sum_add_distrib]

theorem growth_loads_nonempty (B : Matrix ι ι ℝ) (p : ι) :
    ∃ x : ℝ, 0 ≤ x ∧ DUnstable (loadCore B p x) := by
  refine ⟨|B.trace|+1, by positivity, ?_⟩
  apply hurwitzUnstable_implies_dUnstable
  apply unstable_of_trace_pos
  rw [load_trace]
  linarith [neg_abs_le B.trace]

end
end DStabilityCharacterization.Granularity
