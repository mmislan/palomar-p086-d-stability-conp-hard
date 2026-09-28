module

public import proofs.DStabilityHardness.Encoding

@[expose] public section

/-!
# Paper root: *Deciding D-stability is coNP-hard*

This module imports exactly the critical path of the paper (not the follow-up modules
`TimeScale`, `Classification`).  It adds the promise-problem form of the main theorem: the
integer matrix of the reduction is D-stable and D-semistable when the PARTITION instance is a
no-instance, and strictly D-unstable, not D-semistable and not D-stable when it is a yes-instance.
-/

namespace DStabilityHardness

open DUnstableCores

/-- The base point of the continuation has no window. -/
theorem Wd_base_neg : Wd (17 / 10) < 0 := by
  unfold Wd
  rw [disc_factor]
  apply div_neg_of_neg_of_pos
  · unfold gam; norm_num
  · unfold k2; norm_num

/-- **Main theorem, promise form.** With `N = max(8T, 4)`, `(p, q)` the first Pell pair of the
recursion with `q ≥ N`, and `M` the integer matrix `hardIntMatrix p q w T` (cast to `ℝ`):
the search takes at most `log₃ N + 1` steps, `q ≤ 4N + 1`, every entry satisfies
`|M_ij| ≤ 720 q³ T`, and
* if no subset of `w` sums to `T`, then `M` is D-stable and D-semistable;
* if some subset sums to `T`, then `M` is strictly D-unstable, hence neither D-stable nor
  D-semistable. -/
theorem partition_dichotomy {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (w : κ → ℕ) (hw : ∀ j, 0 < w j) (T : ℕ) (hT : ∑ j, w j = 2 * T) :
    pellIndex (max (8 * T) 4) ≤ Nat.log 3 (max (8 * T) 4) + 1 ∧
    (pellSeq (pellIndex (max (8 * T) 4))).2 ≤ 4 * max (8 * T) 4 + 1 ∧
    (∀ i j, |hardIntMatrix (pellSeq (pellIndex (max (8 * T) 4))).1
        (pellSeq (pellIndex (max (8 * T) 4))).2 w T i j|
      ≤ 720 * ((pellSeq (pellIndex (max (8 * T) 4))).2 : ℤ) ^ 3 * T) ∧
    ((¬ ∃ S : Finset κ, ∑ j ∈ S, w j = T) →
      DStable ((hardIntMatrix (pellSeq (pellIndex (max (8 * T) 4))).1
        (pellSeq (pellIndex (max (8 * T) 4))).2 w T).map (Int.cast : ℤ → ℝ)) ∧
      DNonUnstable ((hardIntMatrix (pellSeq (pellIndex (max (8 * T) 4))).1
        (pellSeq (pellIndex (max (8 * T) 4))).2 w T).map (Int.cast : ℤ → ℝ))) ∧
    ((∃ S : Finset κ, ∑ j ∈ S, w j = T) →
      DUnstable ((hardIntMatrix (pellSeq (pellIndex (max (8 * T) 4))).1
        (pellSeq (pellIndex (max (8 * T) 4))).2 w T).map (Int.cast : ℤ → ℝ)) ∧
      ¬ DNonUnstable ((hardIntMatrix (pellSeq (pellIndex (max (8 * T) 4))).1
        (pellSeq (pellIndex (max (8 * T) 4))).2 w T).map (Int.cast : ℤ → ℝ)) ∧
      ¬ DStable ((hardIntMatrix (pellSeq (pellIndex (max (8 * T) 4))).1
        (pellSeq (pellIndex (max (8 * T) 4))).2 w T).map (Int.cast : ℤ → ℝ))) := by
  obtain ⟨hk, hq, hb, hiff, hyes⟩ := dStability_coNP_reduction w hw T hT
  refine ⟨hk, hq, hb, fun hno => ?_, fun hS => ?_⟩
  · have hs := hiff.mpr hno
    exact ⟨hs, dStable_implies_dNonUnstable _ hs⟩
  · have hu := hyes hS
    refine ⟨hu, (not_dNonUnstable_iff_dUnstable _).mpr hu, fun hs => ?_⟩
    exact ((not_dNonUnstable_iff_dUnstable _).mpr hu) (dStable_implies_dNonUnstable _ hs)

end DStabilityHardness
