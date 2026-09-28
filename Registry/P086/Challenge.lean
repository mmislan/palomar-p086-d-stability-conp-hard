module
public import Mathlib

/-! Integer PARTITION reduction and the strict stability dichotomy. -/
@[expose] public section
noncomputable section
open scoped BigOperators

namespace DUnstableCores
variable {ι : Type*}

/-- Right diagonal scaling: multiply column j by the positive-rate coordinate d j. -/
def rightScale (A : Matrix ι ι ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => A i j * d j

/-- Embed a real matrix entrywise into the complex numbers. -/
def complexify (A : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  fun i j => (A i j : ℂ)

/-- A nonzero complex vector satisfying the matrix eigenvalue equation. -/
def HasEigenpair [Fintype ι] (A : Matrix ι ι ℝ) (lam : ℂ) (v : ι → ℂ) : Prop :=
  v ≠ 0 ∧ ∀ i, Matrix.mulVec (complexify A) v i = lam * v i

/-- Existence of an eigenvalue with strictly positive real part. -/
def HurwitzUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ lam : ℂ, ∃ v : ι → ℂ, 0 < lam.re ∧ HasEigenpair A lam v

/-- Absence of strictly positive-real-part eigenvalues; imaginary-axis roots are allowed. -/
def HurwitzNonpositive [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ¬ HurwitzUnstable A

/-- Every complex eigenvalue has strictly negative real part. -/
def HurwitzStable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ lam : ℂ, ∀ v : ι → ℂ, HasEigenpair A lam v → lam.re < 0

/-- Some strictly positive right diagonal scaling is strictly Hurwitz-unstable. -/
def DUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧ HurwitzUnstable (rightScale A d)

/-- Every strictly positive right diagonal scaling is Hurwitz-stable. -/
def DStable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ d : ι → ℝ, (∀ i, 0 < d i) → HurwitzStable (rightScale A d)

/-- Every strictly positive right diagonal scaling has no strict growth. -/
def DNonUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ d : ι → ℝ, (∀ i, 0 < d i) → HurwitzNonpositive (rightScale A d)

end DUnstableCores

namespace DStabilityHardness
open DUnstableCores

/-- The fourth coordinate, indexed by 3, is the reduction core attachment port. -/
abbrev port : Fin 4 := 3

/-- Positive common-denominator expression 10*q*(9*q^2-4)*T for admissible reduction inputs. -/
def encD (q T : ℕ) : ℤ := 10 * q * (9 * (q : ℤ) ^ 2 - 4) * T

/-- The literal four-by-four integer core of the PARTITION reduction. -/
def coreInt (p q T : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-encD q T, -(4 * q * (9 * (q : ℤ) ^ 2 - 4) * T), -(4 * q * (9 * (q : ℤ) ^ 2 - 4) * T),
      -encD q T;
     8 * T * (3 * p + 4 * q) * (9 * (q : ℤ) ^ 2 - 4), -encD q T,
      -(4 * q * (9 * (q : ℤ) ^ 2 - 4) * T), -encD q T;
     8 * T * (3 * p + 4 * q) * (9 * (q : ℤ) ^ 2 - 4), 8 * T * (3 * p + 4 * q) * (9 * (q : ℤ) ^ 2 - 4),
      -encD q T, -encD q T;
     -encD q T, -encD q T, -encD q T, -(5 * T * q * (15 * p * q + 54 * (q : ℤ) ^ 2 - 14))]

/-- The integer reduction matrix of dimension 4+|kappa|, with one leaf per input weight. -/
def hardIntMatrix {κ : Type*} [DecidableEq κ] (p q : ℕ) (w : κ → ℕ) (T : ℕ) :
    Matrix (Fin 4 ⊕ κ) (Fin 4 ⊕ κ) ℤ
  | .inl i, .inl j => coreInt p q T i j
  | .inl i, .inr j => if i = port then 5 * q * (9 * (q : ℤ) ^ 2 - 4) * w j else 0
  | .inr _, .inl j => if j = port then encD q T else 0
  | .inr i, .inr j => if i = j then -encD q T else 0

/-- Pell recursion beginning at (2,1) and sending (p,q) to (2p+3q,p+2q). -/
def pellSeq : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | k + 1 => (2 * (pellSeq k).1 + 3 * (pellSeq k).2, (pellSeq k).1 + 2 * (pellSeq k).2)

theorem pell_step {p q : ℕ} (h : p ^ 2 = 3 * q ^ 2 + 1) :
    (2 * p + 3 * q) ^ 2 = 3 * (p + 2 * q) ^ 2 + 1 := by
  nlinarith [h]

theorem pellSeq_pell (k : ℕ) : (pellSeq k).1 ^ 2 = 3 * (pellSeq k).2 ^ 2 + 1 := by
  induction k with
  | zero => simp [pellSeq]
  | succ k ih => simp only [pellSeq]; exact pell_step ih

theorem pellSeq_q_le_p (k : ℕ) : (pellSeq k).2 ≤ (pellSeq k).1 := by
  have h := pellSeq_pell k
  by_contra hc
  push Not at hc
  have : (pellSeq k).1 ^ 2 < (pellSeq k).2 ^ 2 := Nat.pow_lt_pow_left hc (by norm_num)
  omega

theorem pellSeq_three_pow (k : ℕ) : 3 ^ k ≤ (pellSeq k).2 := by
  induction k with
  | zero => simp [pellSeq]
  | succ k ih =>
    have := pellSeq_q_le_p k
    simp only [pellSeq, pow_succ]
    omega

theorem exists_pell_ge (N : ℕ) : ∃ k, N ≤ (pellSeq k).2 :=
  ⟨N, le_trans (Nat.lt_pow_self (by norm_num : 1 < 3)).le (pellSeq_three_pow N)⟩

/-- Least Pell-recursion index whose second coordinate is at least N. -/
def pellIndex (N : ℕ) : ℕ := Nat.find (exists_pell_ge N)

/-- An explicit integer matrix reduction from positive nonempty PARTITION instances of total weight 2T, with a logarithmic Pell-search bound, bounded output entries, D-stability exactly when no equal split exists, and strict D-instability when an equal split exists. -/
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
  sorry

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
  sorry

end DStabilityHardness

end
