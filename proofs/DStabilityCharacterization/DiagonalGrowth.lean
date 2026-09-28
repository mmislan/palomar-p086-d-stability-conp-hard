module

public import proofs.DStabilityCharacterization.TraceGrowth

@[expose] public section

namespace DStabilityCharacterization.Granularity
open DUnstableCores
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dUnstable_of_diagonal_pos (B : Matrix ι ι ℝ) (p : ι) (hp : 0<B p p) :
    DUnstable B := by
  let N : ℝ := |B.trace|+1
  let d : ι → ℝ := fun i => 1+if i=p then N/B p p else 0
  have hN : 0<N := by dsimp [N]; positivity
  have hd : ∀ i, 0<d i := by
    intro i
    dsimp [d]
    split_ifs
    · linarith [div_pos hN hp]
    · norm_num
  refine ⟨d,hd,unstable_of_trace_pos _ ?_⟩
  have htrace : (rightScale B d).trace=B.trace+N := by
    change (∑ i, B i i * (1 + if i=p then N/B p p else 0)) = (∑ i, B i i)+N
    simp only [mul_add, mul_one, mul_ite, mul_zero, Finset.sum_add_distrib]
    simp
    field_simp
  rw [htrace]
  dsimp [N]
  linarith [neg_abs_le B.trace]

theorem diagonal_nonpos_of_dStable (B : Matrix ι ι ℝ) (hB : DStable B) (p : ι) :
    B p p ≤ 0 := by
  by_contra! hp
  obtain ⟨d,hd,hu⟩ := dUnstable_of_diagonal_pos B p hp
  obtain ⟨z,v,hz,hv⟩ := hu
  have hh := hB d hd z v hv
  linarith

theorem load_unstable_above_diagonal (B : Matrix ι ι ℝ) (p : ι) (x : ℝ)
    (hx : -B p p<x) : DUnstable (loadCore B p x) := by
  apply dUnstable_of_diagonal_pos _ p
  simp only [loadCore, and_self, ite_true]
  linarith

end
end DStabilityCharacterization.Granularity
