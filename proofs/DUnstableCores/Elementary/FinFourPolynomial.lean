module

public import proofs.DUnstableCores.CharPoly

@[expose] public section

namespace DUnstableCores
open Polynomial

def elementaryMinor3 (A : Matrix (Fin 4) (Fin 4) ℝ) (i j k : Fin 4) : ℝ :=
  A i i*A j j*A k k - A i i*A j k*A k j -
  A i j*A j i*A k k + A i j*A j k*A k i +
  A i k*A j i*A k j - A i k*A j j*A k i

def elementaryCoeff1 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  -(A 0 0+A 1 1+A 2 2+A 3 3)
def elementaryCoeff2 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (A 0 0*A 1 1-A 0 1*A 1 0)+(A 0 0*A 2 2-A 0 2*A 2 0)+
  (A 0 0*A 3 3-A 0 3*A 3 0)+(A 1 1*A 2 2-A 1 2*A 2 1)+
  (A 1 1*A 3 3-A 1 3*A 3 1)+(A 2 2*A 3 3-A 2 3*A 3 2)
def elementaryCoeff3 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  -(elementaryMinor3 A 0 1 2+elementaryMinor3 A 0 1 3+
    elementaryMinor3 A 0 2 3+elementaryMinor3 A 1 2 3)
def elementaryMinorBlock3 (A : Matrix (Fin 4) (Fin 4) ℝ)
    (i j k r s t : Fin 4) : ℝ :=
  A i r*A j s*A k t - A i r*A j t*A k s -
  A i s*A j r*A k t + A i s*A j t*A k r +
  A i t*A j r*A k s - A i t*A j s*A k r
def elementaryCoeff4 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  A 0 0*elementaryMinorBlock3 A 1 2 3 1 2 3 -
  A 0 1*elementaryMinorBlock3 A 1 2 3 0 2 3 +
  A 0 2*elementaryMinorBlock3 A 1 2 3 0 1 3 -
  A 0 3*elementaryMinorBlock3 A 1 2 3 0 1 2

theorem elementary_charpoly_fin4 (A : Matrix (Fin 4) (Fin 4) ℝ) :
    A.charpoly = X^4+C (elementaryCoeff1 A)*X^3+
      C (elementaryCoeff2 A)*X^2+C (elementaryCoeff3 A)*X+C (elementaryCoeff4 A) := by
  unfold Matrix.charpoly Matrix.charmatrix elementaryCoeff1 elementaryCoeff2
    elementaryCoeff3 elementaryCoeff4 elementaryMinor3 elementaryMinorBlock3
  rw [Matrix.det_succ_row_zero]
  have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := rfl
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := rfl
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := rfl
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, h12,h22,h32]
  ring

end DUnstableCores
