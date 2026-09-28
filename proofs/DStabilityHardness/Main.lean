module

public import proofs.DStabilityHardness.Reduction

@[expose] public section

/-!
# T-HARD: final statement with the Pell size bound

`pell_exists N` gives a solution of `p² = 3q² + 1` with `N ≤ q ≤ 4N + 1`; it is produced by the
recursion `(p, q) ↦ (2p + 3q, p + 2q)` started at `(2, 1)`, so `q` has `O(log N)` bits and the
reduction's output has polynomial bit size.  `dStability_partition_reduction` combines this with
`hardness_iff`/`hardness_reduction`.
-/

namespace DStabilityHardness

open DUnstableCores

/-- One Pell step preserves `p² = 3q² + 1`. -/
theorem pell_step {p q : ℕ} (h : p ^ 2 = 3 * q ^ 2 + 1) :
    (2 * p + 3 * q) ^ 2 = 3 * (p + 2 * q) ^ 2 + 1 := by
  nlinarith [h]

theorem pell_le_two {p q : ℕ} (h : p ^ 2 = 3 * q ^ 2 + 1) (hq : 1 ≤ q) : p ≤ 2 * q := by
  by_contra hc
  push Not at hc
  have : (2 * q + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hc 2
  nlinarith

/-- Pell solutions of every size, with at most a factor-four overshoot. -/
theorem pell_exists (N : ℕ) :
    ∃ p q : ℕ, p ^ 2 = 3 * q ^ 2 + 1 ∧ 1 ≤ q ∧ N ≤ q ∧ q ≤ 4 * N + 1 := by
  induction N with
  | zero => exact ⟨2, 1, by norm_num, le_rfl, by norm_num, by norm_num⟩
  | succ n ih =>
    obtain ⟨p, q, h, hq1, hn, hq⟩ := ih
    by_cases hlt : n + 1 ≤ q
    · exact ⟨p, q, h, hq1, hlt, by omega⟩
    · have hqn : q = n := by omega
      have hp2 := pell_le_two h hq1
      have hp1 : 1 ≤ p := by nlinarith
      exact ⟨2 * p + 3 * q, p + 2 * q, pell_step h, by omega, by omega, by omega⟩

/-- **Main theorem (T-HARD).** For every PARTITION instance `w` (positive weights, total `2T`)
there is a Pell pair `(p, q)` with `max(8T, 4) ≤ q ≤ 4 max(8T, 4) + 1` such that the explicit
rational star matrix `hardMatrix p q w T` is D-stable iff no subset of `w` sums to `T`, and is
strictly D-unstable (a positive scaling has an eigenvalue with positive real part) otherwise. -/
theorem dStability_partition_reduction {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (w : κ → ℕ) (hw : ∀ j, 0 < w j) (T : ℕ) (hT : ∑ j, w j = 2 * T) :
    ∃ p q : ℕ, p ^ 2 = 3 * q ^ 2 + 1 ∧ max (8 * T) 4 ≤ q ∧ q ≤ 4 * max (8 * T) 4 + 1 ∧
      (DStable (hardMatrix p q w T) ↔ ¬ ∃ S : Finset κ, ∑ j ∈ S, w j = T) ∧
      ((∃ S : Finset κ, ∑ j ∈ S, w j = T) → DUnstable (hardMatrix p q w T)) := by
  obtain ⟨p, q, h, -, hlo, hhi⟩ := pell_exists (max (8 * T) 4)
  have h8 : 8 * T ≤ q := le_trans (le_max_left _ _) hlo
  have h4 : 4 ≤ q := le_trans (le_max_right _ _) hlo
  exact ⟨p, q, h, hlo, hhi, hardness_iff w hw T hT p q h h8 h4,
    (hardness_reduction w hw T hT p q h h8 h4).2⟩

end DStabilityHardness
