module

public import proofs.DStabilityHardness.Main

@[expose] public section

/-!
# Explicit integer encoding of the reduction

The reduction's output `hardMatrix p q w T` is a positive real multiple of an explicit **integer**
matrix `hardIntMatrix p q w T`, whose entries are polynomials in `p, q, T, w_j` of degree ≤ 3 in
`q`; the Pell pair is produced by the recursion `(p, q) ↦ (2p + 3q, p + 2q)` in at most
`log₃ N + 1` steps with `q ≤ 4N + 1`.  Since D-stability and strict D-instability are invariant
under multiplication by a positive scalar, the reduction theorem holds verbatim for the integer
matrix.  `dStability_coNP_reduction` is the final statement.
-/

namespace DStabilityHardness

open DUnstableCores DStabilityCharacterization.Granularity
open scoped BigOperators

noncomputable section

/-! ## Invariance under a positive scalar -/

theorem rightScale_smul {ι : Type*} (A : Matrix ι ι ℝ) (c : ℝ) (d : ι → ℝ) :
    rightScale (c • A) d = rightScale A (fun i => c * d i) := by
  ext i j; simp [rightScale]; ring

theorem dStable_smul_iff {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) {c : ℝ} (hc : 0 < c) :
    DStable (c • A) ↔ DStable A := by
  constructor
  · intro h d hd
    have e : d = fun i => c * (c⁻¹ * d i) := by funext i; field_simp
    rw [e, ← rightScale_smul]
    exact h _ (fun i => mul_pos (inv_pos.mpr hc) (hd i))
  · intro h d hd
    rw [rightScale_smul]
    exact h _ (fun i => mul_pos hc (hd i))

theorem dUnstable_smul_iff {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) {c : ℝ} (hc : 0 < c) :
    DUnstable (c • A) ↔ DUnstable A := by
  constructor
  · rintro ⟨d, hd, hu⟩
    rw [rightScale_smul] at hu
    exact ⟨_, fun i => mul_pos hc (hd i), hu⟩
  · rintro ⟨d, hd, hu⟩
    refine ⟨fun i => c⁻¹ * d i, fun i => mul_pos (inv_pos.mpr hc) (hd i), ?_⟩
    rw [rightScale_smul]
    have e : (fun i => c * (c⁻¹ * d i)) = d := by funext i; field_simp
    rw [e]; exact hu

/-! ## The explicit integer matrix -/

/-- Common denominator `D = 10 q (9q² − 4) T`. -/
def encD (q T : ℕ) : ℤ := 10 * q * (9 * (q : ℤ) ^ 2 - 4) * T

def coreInt (p q T : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-encD q T, -(4 * q * (9 * (q : ℤ) ^ 2 - 4) * T), -(4 * q * (9 * (q : ℤ) ^ 2 - 4) * T),
      -encD q T;
     8 * T * (3 * p + 4 * q) * (9 * (q : ℤ) ^ 2 - 4), -encD q T,
      -(4 * q * (9 * (q : ℤ) ^ 2 - 4) * T), -encD q T;
     8 * T * (3 * p + 4 * q) * (9 * (q : ℤ) ^ 2 - 4), 8 * T * (3 * p + 4 * q) * (9 * (q : ℤ) ^ 2 - 4),
      -encD q T, -encD q T;
     -encD q T, -encD q T, -encD q T, -(5 * T * q * (15 * p * q + 54 * (q : ℤ) ^ 2 - 14))]

/-- The reduction's output as an integer matrix (dimension `4 + |κ|`). -/
def hardIntMatrix {κ : Type*} [DecidableEq κ] (p q : ℕ) (w : κ → ℕ) (T : ℕ) :
    Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) ℤ
  | .inl i, .inl j => coreInt p q T i j
  | .inl i, .inr j => if i = port then 5 * q * (9 * (q : ℤ) ^ 2 - 4) * w j else 0
  | .inr _, .inl j => if j = port then encD q T else 0
  | .inr i, .inr j => if i = j then -encD q T else 0

theorem hv_eq (ρ : ℝ) (hk : 4 * ρ ^ 2 - 21 ≠ 0) :
    hv ρ = 5 * (2 * ρ ^ 2 - 3 * ρ - 15) / (2 * (4 * ρ ^ 2 - 21)) := by
  have hk' : 2 * (72 * (21 - 4 * ρ ^ 2) / 125) ≠ 0 := by
    intro h; apply hk; linarith
  unfold hv k1 k2
  rw [div_eq_div_iff hk' (mul_ne_zero two_ne_zero hk)]
  ring

/-- The window-centre offset `h₀ = h_v + 1/2` in closed form on Pell pairs. -/
theorem h0_formula (p q : ℕ) (hpell : p ^ 2 = 3 * q ^ 2 + 1) (hq : 1 ≤ q) :
    hv ((p : ℝ) / q) + 1 / 2 =
      (54 * (q : ℝ) ^ 2 + 15 * p * q - 14) / (2 * (9 * (q : ℝ) ^ 2 - 4)) := by
  have hq0 : (q : ℝ) ≠ 0 := by have : (0 : ℝ) < q := by exact_mod_cast hq
                               exact ne_of_gt this
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp : ((p : ℝ)) ^ 2 = 3 * (q : ℝ) ^ 2 + 1 := by exact_mod_cast hpell
  have h9 : (0 : ℝ) < 9 * (q : ℝ) ^ 2 - 4 := by nlinarith
  have hsq : ((p : ℝ) / q) ^ 2 = 3 + 1 / (q : ℝ) ^ 2 := by rw [div_pow, hp]; field_simp
  have hk : 4 * ((p : ℝ) / q) ^ 2 - 21 ≠ 0 := by
    rw [hsq]
    have : 4 * (3 + 1 / (q : ℝ) ^ 2) - 21 = -(9 * (q : ℝ) ^ 2 - 4) / (q : ℝ) ^ 2 := by
      field_simp; ring
    rw [this]; exact div_ne_zero (by linarith) (by positivity)
  -- clear the `q`-denominators
  have hscale : 5 * (2 * ((p : ℝ) / q) ^ 2 - 3 * ((p : ℝ) / q) - 15) / (2 * (4 * ((p : ℝ) / q) ^ 2 - 21))
      = 5 * (2 * (p : ℝ) ^ 2 - 3 * p * q - 15 * (q : ℝ) ^ 2) / (2 * (4 * (p : ℝ) ^ 2 - 21 * (q : ℝ) ^ 2)) := by
    have hk2 : 2 * (4 * (p : ℝ) ^ 2 - 21 * (q : ℝ) ^ 2) ≠ 0 := by
      rw [hp]; nlinarith
    rw [div_eq_div_iff (mul_ne_zero two_ne_zero hk) hk2]
    field_simp
  rw [hv_eq _ hk, hscale, hp]
  have hb : (2 : ℝ) * (4 * (3 * (q : ℝ) ^ 2 + 1) - 21 * (q : ℝ) ^ 2) ≠ 0 := by nlinarith
  have hc : (2 : ℝ) * (9 * (q : ℝ) ^ 2 - 4) ≠ 0 := by positivity
  rw [div_add_div _ _ hb two_ne_zero, div_eq_div_iff (mul_ne_zero hb two_ne_zero) hc]
  ring

theorem hardIntMatrix_cast {κ : Type*} [DecidableEq κ] (p q : ℕ) (w : κ → ℕ) (T : ℕ)
    (hpell : p ^ 2 = 3 * q ^ 2 + 1) (hq : 1 ≤ q) (hT : 0 < T) :
    (hardIntMatrix p q w T).map (Int.cast : ℤ → ℝ) = ((encD q T : ℤ) : ℝ) • hardMatrix p q w T := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have h9 : (0 : ℝ) < 9 * (q : ℝ) ^ 2 - 4 := by nlinarith
  have hh0 := h0_formula p q hpell hq
  have h9a : (9 * (q : ℝ) ^ 2 - 4) ≠ 0 := ne_of_gt h9
  have h9b : (-4 + (q : ℝ) ^ 2 * 9) ≠ 0 := by intro h; apply h9a; linarith
  have h9c : ((q : ℝ) ^ 2 * 9 - 4) ≠ 0 := by intro h; apply h9a; linarith
  unfold hardMatrix
  rw [hh0]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hardIntMatrix,
      attached]
    fin_cases i <;> fin_cases j <;>
      simp [coreInt, coreB, encD, gam] <;> field_simp <;> ring
  · simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hardIntMatrix,
      attached, hardLoads]
    split_ifs <;> simp [encD]
    field_simp
    ring
  · simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hardIntMatrix,
      attached]
    split_ifs <;> simp [encD]
  · simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hardIntMatrix,
      attached]
    split_ifs <;> simp [encD]

theorem encD_pos (q T : ℕ) (hq : 1 ≤ q) (hT : 0 < T) : (0 : ℝ) < ((encD q T : ℤ) : ℝ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  unfold encD; push_cast
  have : (0 : ℝ) < 9 * (q : ℝ) ^ 2 - 4 := by nlinarith
  positivity

/-! ## Efficient Pell search -/

def pellSeq : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | k + 1 => (2 * (pellSeq k).1 + 3 * (pellSeq k).2, (pellSeq k).1 + 2 * (pellSeq k).2)

theorem pellSeq_pell (k : ℕ) : (pellSeq k).1 ^ 2 = 3 * (pellSeq k).2 ^ 2 + 1 := by
  induction k with
  | zero => simp [pellSeq]
  | succ k ih => simp only [pellSeq]; exact pell_step ih

theorem pellSeq_q_pos (k : ℕ) : 1 ≤ (pellSeq k).2 := by
  induction k with
  | zero => simp [pellSeq]
  | succ k ih => simp only [pellSeq]; omega

theorem pellSeq_q_le_p (k : ℕ) : (pellSeq k).2 ≤ (pellSeq k).1 := by
  cases k with
  | zero => exact Nat.le_succ 1
  | succ k =>
    change (pellSeq k).1 + 2 * (pellSeq k).2 ≤
      2 * (pellSeq k).1 + 3 * (pellSeq k).2
    apply Nat.add_le_add
    · calc
        (pellSeq k).1 = 1 * (pellSeq k).1 := (Nat.one_mul _).symm
        _ ≤ 2 * (pellSeq k).1 := Nat.mul_le_mul_right _ (Nat.le_succ 1)
    · exact Nat.mul_le_mul_right _ (Nat.le_succ 2)

theorem pellSeq_p_le (k : ℕ) : (pellSeq k).1 ≤ 2 * (pellSeq k).2 :=
  pell_le_two (pellSeq_pell k) (pellSeq_q_pos k)

theorem pellSeq_three_pow (k : ℕ) : 3 ^ k ≤ (pellSeq k).2 := by
  induction k with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
    change 3 ^ (k + 1) ≤ (pellSeq k).1 + 2 * (pellSeq k).2
    calc
      3 ^ (k + 1) = 3 ^ k * 3 := Nat.pow_succ 3 k
      _ ≤ (pellSeq k).2 * 3 := Nat.mul_le_mul_right 3 ih
      _ = (pellSeq k).2 * 2 + (pellSeq k).2 := Nat.mul_succ _ 2
      _ = 2 * (pellSeq k).2 + (pellSeq k).2 :=
        congrArg (fun x => x + (pellSeq k).2) (Nat.mul_comm _ 2)
      _ = (pellSeq k).2 + 2 * (pellSeq k).2 := Nat.add_comm _ _
      _ ≤ (pellSeq k).1 + 2 * (pellSeq k).2 :=
        Nat.add_le_add_right (pellSeq_q_le_p k) _

theorem exists_pell_ge (N : ℕ) : ∃ k, N ≤ (pellSeq k).2 :=
  ⟨N, le_trans (Nat.lt_pow_self (by norm_num : 1 < 3)).le (pellSeq_three_pow N)⟩

/-- Index of the first Pell pair with `q ≥ N`. -/
def pellIndex (N : ℕ) : ℕ := Nat.find (exists_pell_ge N)

theorem pellIndex_spec (N : ℕ) : N ≤ (pellSeq (pellIndex N)).2 := Nat.find_spec (exists_pell_ge N)

/-- The search takes at most `log₃ N + 1` Pell steps. -/
theorem pellIndex_le_log (N : ℕ) : pellIndex N ≤ Nat.log 3 N + 1 := by
  apply Nat.find_min'
  exact le_trans (Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) N).le
    (pellSeq_three_pow _)

theorem pellIndex_q_le (N : ℕ) : (pellSeq (pellIndex N)).2 ≤ 4 * N + 1 := by
  rcases Nat.eq_zero_or_pos (pellIndex N) with h | h
  · rw [h]; simp [pellSeq]
  · obtain ⟨k, hk⟩ : ∃ k, pellIndex N = k + 1 := ⟨pellIndex N - 1, by omega⟩
    have hmin : ¬ N ≤ (pellSeq k).2 := Nat.find_min (exists_pell_ge N) (by
      change k < pellIndex N; omega)
    rw [hk]
    have := pellSeq_p_le k
    simp only [pellSeq]
    omega

/-! ## Entry bounds -/

theorem coreInt_cases (p q T : ℕ) (i j : Fin 4) :
    coreInt p q T i j = -encD q T ∨
    coreInt p q T i j = -(4 * q * (9 * (q : ℤ) ^ 2 - 4) * T) ∨
    coreInt p q T i j = 8 * T * (3 * p + 4 * q) * (9 * (q : ℤ) ^ 2 - 4) ∨
    coreInt p q T i j = -(5 * T * q * (15 * p * q + 54 * (q : ℤ) ^ 2 - 14)) := by
  fin_cases i <;> fin_cases j <;> simp [coreInt]

theorem hardIntMatrix_bound {κ : Type*} [DecidableEq κ] (p q : ℕ) (w : κ → ℕ) (T : ℕ)
    (hq : 1 ≤ q) (hpq : p ≤ 2 * q) (hw : ∀ j, w j ≤ 2 * T) :
    ∀ i j, |hardIntMatrix p q w T i j| ≤ 720 * (q : ℤ) ^ 3 * T := by
  have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hpq' : (p : ℤ) ≤ 2 * q := by exact_mod_cast hpq
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hT0 : (0 : ℤ) ≤ T := by positivity
  have h9 : (0 : ℤ) ≤ 9 * (q : ℤ) ^ 2 - 4 := by nlinarith
  have h9' : 9 * (q : ℤ) ^ 2 - 4 ≤ 9 * (q : ℤ) ^ 2 := by linarith
  have hq3 : (0 : ℤ) ≤ (q : ℤ) ^ 3 := by positivity
  have hD0 : 0 ≤ encD q T := by unfold encD; positivity
  have hD1 : encD q T ≤ 720 * (q : ℤ) ^ 3 * T := by
    unfold encD
    have : 10 * (q : ℤ) * (9 * (q : ℤ) ^ 2 - 4) ≤ 90 * (q : ℤ) ^ 3 := by nlinarith
    nlinarith
  have hA0 : 0 ≤ 4 * (q : ℤ) * (9 * (q : ℤ) ^ 2 - 4) * T := by positivity
  have hA1 : 4 * (q : ℤ) * (9 * (q : ℤ) ^ 2 - 4) * T ≤ 720 * (q : ℤ) ^ 3 * T := by
    have : 4 * (q : ℤ) * (9 * (q : ℤ) ^ 2 - 4) ≤ 720 * (q : ℤ) ^ 3 := by nlinarith
    nlinarith
  have hG0 : 0 ≤ 8 * (T : ℤ) * (3 * p + 4 * q) * (9 * (q : ℤ) ^ 2 - 4) := by positivity
  have hG1 : 8 * (T : ℤ) * (3 * p + 4 * q) * (9 * (q : ℤ) ^ 2 - 4) ≤ 720 * (q : ℤ) ^ 3 * T := by
    have h1 : (3 * (p : ℤ) + 4 * q) ≤ 10 * q := by linarith
    have h2 : (3 * (p : ℤ) + 4 * q) * (9 * (q : ℤ) ^ 2 - 4) ≤ 10 * q * (9 * (q : ℤ) ^ 2) := by
      apply mul_le_mul h1 h9' h9 (by positivity)
    nlinarith
  have hH0 : 0 ≤ 5 * (T : ℤ) * q * (15 * p * q + 54 * (q : ℤ) ^ 2 - 14) := by
    have : (0 : ℤ) ≤ 15 * p * q + 54 * (q : ℤ) ^ 2 - 14 := by nlinarith
    positivity
  have hH1 : 5 * (T : ℤ) * q * (15 * p * q + 54 * (q : ℤ) ^ 2 - 14) ≤ 720 * (q : ℤ) ^ 3 * T := by
    have h1 : 15 * (p : ℤ) * q + 54 * (q : ℤ) ^ 2 - 14 ≤ 84 * (q : ℤ) ^ 2 := by nlinarith
    have h2 : (q : ℤ) * (15 * p * q + 54 * (q : ℤ) ^ 2 - 14) ≤ q * (84 * (q : ℤ) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [hardIntMatrix]
    rcases coreInt_cases p q T i j with h | h | h | h <;> rw [h]
    · rw [abs_neg, abs_of_nonneg hD0]; exact hD1
    · rw [abs_neg, abs_of_nonneg hA0]; exact hA1
    · rw [abs_of_nonneg hG0]; exact hG1
    · rw [abs_neg, abs_of_nonneg hH0]; exact hH1
  · simp only [hardIntMatrix]
    split_ifs
    · have hwj : (w j : ℤ) ≤ 2 * T := by exact_mod_cast hw j
      have hw0 : (0 : ℤ) ≤ w j := by positivity
      rw [abs_of_nonneg (by positivity)]
      have : 5 * (q : ℤ) * (9 * (q : ℤ) ^ 2 - 4) ≤ 45 * (q : ℤ) ^ 3 := by nlinarith
      nlinarith
    · simp; positivity
  · simp only [hardIntMatrix]
    split_ifs
    · rw [abs_of_nonneg hD0]; exact hD1
    · simp; positivity
  · simp only [hardIntMatrix]
    split_ifs
    · rw [abs_neg, abs_of_nonneg hD0]; exact hD1
    · simp; positivity

/-! ## Final statement -/

/-- **T-HARD, integer form.** For every PARTITION instance `w` (positive weights, total `2T`), let
`N = max(8T, 4)` and let `(p, q)` be the first Pell pair of the recursion with `q ≥ N` (found in at
most `log₃ N + 1` steps, with `q ≤ 4N + 1`).  The integer matrix `hardIntMatrix p q w T`, of
dimension `4 + m` and with entries bounded by `720 q³ T`, is D-stable iff no subset of `w` sums to
`T`, and strictly D-unstable otherwise. -/
theorem dStability_coNP_reduction {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (w : κ → ℕ) (hw : ∀ j, 0 < w j) (T : ℕ) (hT : ∑ j, w j = 2 * T) :
    pellIndex (max (8 * T) 4) ≤ Nat.log 3 (max (8 * T) 4) + 1 ∧
    (pellSeq (pellIndex (max (8 * T) 4))).2 ≤ 4 * max (8 * T) 4 + 1 ∧
    (∀ i j, |hardIntMatrix (pellSeq (pellIndex (max (8 * T) 4))).1
        (pellSeq (pellIndex (max (8 * T) 4))).2 w T i j|
      ≤ 720 * ((pellSeq (pellIndex (max (8 * T) 4))).2 : ℤ) ^ 3 * T) ∧
    (DStable ((hardIntMatrix (pellSeq (pellIndex (max (8 * T) 4))).1
        (pellSeq (pellIndex (max (8 * T) 4))).2 w T).map (Int.cast : ℤ → ℝ)) ↔
      ¬ ∃ S : Finset κ, ∑ j ∈ S, w j = T) ∧
    ((∃ S : Finset κ, ∑ j ∈ S, w j = T) →
      DUnstable ((hardIntMatrix (pellSeq (pellIndex (max (8 * T) 4))).1
        (pellSeq (pellIndex (max (8 * T) 4))).2 w T).map (Int.cast : ℤ → ℝ))) := by
  set N := max (8 * T) 4
  set k := pellIndex N
  set p := (pellSeq k).1
  set q := (pellSeq k).2
  have hpell : p ^ 2 = 3 * q ^ 2 + 1 := pellSeq_pell k
  have hqN : N ≤ q := pellIndex_spec N
  have h8 : 8 * T ≤ q := le_trans (le_max_left _ _) hqN
  have h4 : 4 ≤ q := le_trans (le_max_right _ _) hqN
  obtain ⟨j0⟩ := (inferInstance : Nonempty κ)
  have hTpos : 0 < T := by
    have : w j0 ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j0)
    have := hw j0; omega
  have hwle : ∀ j, w j ≤ 2 * T := fun j => by
    rw [← hT]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
  have hcast := hardIntMatrix_cast p q w T hpell (by omega) hTpos
  have hc := encD_pos q T (by omega) hTpos
  refine ⟨pellIndex_le_log N, pellIndex_q_le N,
    hardIntMatrix_bound p q w T (by omega) (pellSeq_p_le k) hwle, ?_, ?_⟩
  · rw [hcast, dStable_smul_iff _ hc]
    exact hardness_iff w hw T hT p q hpell h8 h4
  · intro hS
    rw [hcast, dUnstable_smul_iff _ hc]
    exact (hardness_reduction w hw T hT p q hpell h8 h4).2 hS

end

end DStabilityHardness
