module

public import proofs.CollectiveInstability.QuarticClassification
public import proofs.DUnstableCores.Elementary.FinFourPolynomial

@[expose] public section

/-!
# The narrow-window core family for the D-stability hardness reduction

`coreB ρ h` is the rational 4×4 core with `α = 2/5`, `β = 1`, `γ = (16+12ρ)/5`; the port is
coordinate `3`.  Its principal minors are equal within each order and type, so the scaled
characteristic polynomial depends on the inner rates only through their elementary symmetric
functions.  This file records the exact algebra: the scaled characteristic polynomial, the
Hurwitz decomposition `Δ₃ = F₀ + F₁ v + F₂ v² + h (m₂ m₃ U + K r) v³`, the disk certificate
identity for `Ψ`, and the discriminant factorization `disc K = (144/25)(α+γ)²(ρ²-3)`.
-/

namespace DStabilityHardness

open DUnstableCores CollectiveInstability Polynomial

set_option linter.unusedVariables false

noncomputable section

/-- The inner feed-forward coefficient as a function of the Pell parameter. -/
def gam (ρ : ℝ) : ℝ := (16 + 12 * ρ) / 5

/-- The core. Port = coordinate `3`, port self-coefficient `-h`. -/
def coreB (ρ h : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, -2/5, -2/5, -1;
     gam ρ, -1, -2/5, -1;
     gam ρ, gam ρ, -1, -1;
     -1, -1, -1, -h]

def e2 (ρ : ℝ) : ℝ := (57 + 24 * ρ) / 25
def e3 (ρ : ℝ) : ℝ := (1053 + 1080 * ρ + 288 * ρ ^ 2) / 125
def m2 (h : ℝ) : ℝ := h - 1
def m3 (ρ h : ℝ) : ℝ := (57 + 24 * ρ) * h / 25 - (24 + 12 * ρ) / 5
def m4 (ρ h : ℝ) : ℝ := e3 ρ * h - (513 + 540 * ρ + 144 * ρ ^ 2) / 25

/-- The port-fast Cain quantity. -/
def Kf (ρ h : ℝ) : ℝ := 9 * m2 h * m3 ρ h - h * m4 ρ h
def k2 (ρ : ℝ) : ℝ := 72 * (21 - 4 * ρ ^ 2) / 125
def k1 (ρ : ℝ) : ℝ := 72 * (2 * ρ ^ 2 - 3 * ρ - 15) / 25
def k0 (ρ : ℝ) : ℝ := 108 * (ρ + 2) / 5

theorem Kf_quadratic (ρ h : ℝ) : Kf ρ h = k2 ρ * h ^ 2 + k1 ρ * h + k0 ρ := by
  unfold Kf m2 m3 m4 e3 k2 k1 k0; ring

theorem k2_eq (ρ : ℝ) : k2 ρ = 9 * e2 ρ - e3 ρ := by unfold k2 e2 e3; ring

/-- Window vertex. -/
def hv (ρ : ℝ) : ℝ := -k1 ρ / (2 * k2 ρ)

/-- Exact discriminant factorization. -/
theorem disc_factor (ρ : ℝ) :
    k1 ρ ^ 2 - 4 * k2 ρ * k0 ρ = 144 / 25 * (2 / 5 + gam ρ) ^ 2 * (ρ ^ 2 - 3) := by
  unfold k1 k2 k0 gam; ring

/-- Completed square around the vertex. -/
theorem Kf_vertex (ρ h : ℝ) (hk : k2 ρ ≠ 0) :
    Kf ρ h = k2 ρ * (h - hv ρ) ^ 2 - (k1 ρ ^ 2 - 4 * k2 ρ * k0 ρ) / (4 * k2 ρ) := by
  rw [Kf_quadratic]; unfold hv; field_simp; ring

/-! ## Scaled characteristic polynomial -/

def sp (x y z : ℝ) : ℝ := x + y + z
def sq (x y z : ℝ) : ℝ := x * y + x * z + y * z
def sr (x y z : ℝ) : ℝ := x * y * z

def c1 (ρ h x y z v : ℝ) : ℝ := sp x y z + h * v
def c2 (ρ h x y z v : ℝ) : ℝ := e2 ρ * sq x y z + m2 h * sp x y z * v
def c3 (ρ h x y z v : ℝ) : ℝ := e3 ρ * sr x y z + m3 ρ h * sq x y z * v
def c4 (ρ h x y z v : ℝ) : ℝ := m4 ρ h * sr x y z * v

theorem scaled_charpoly (ρ h x y z v : ℝ) :
    HasQuarticCharpoly (rightScale (coreB ρ h) ![x, y, z, v])
      (c1 ρ h x y z v) (c2 ρ h x y z v) (c3 ρ h x y z v) (c4 ρ h x y z v) := by
  unfold HasQuarticCharpoly
  rw [elementary_charpoly_fin4]
  have h1 : elementaryCoeff1 (rightScale (coreB ρ h) ![x, y, z, v]) = c1 ρ h x y z v := by
    simp [elementaryCoeff1, coreB, c1, sp]; ring
  have h2 : elementaryCoeff2 (rightScale (coreB ρ h) ![x, y, z, v]) = c2 ρ h x y z v := by
    simp [elementaryCoeff2, coreB, c2, sp, sq, e2, m2, gam]; ring
  have h3 : elementaryCoeff3 (rightScale (coreB ρ h) ![x, y, z, v]) = c3 ρ h x y z v := by
    simp [elementaryCoeff3, elementaryMinor3, coreB, c3, sq, sr, e3, m3, gam]; ring
  have h4 : elementaryCoeff4 (rightScale (coreB ρ h) ![x, y, z, v]) = c4 ρ h x y z v := by
    simp [elementaryCoeff4, elementaryMinorBlock3, coreB, c4, sr, m4, e3, gam]; ring
  rw [h1, h2, h3, h4]

/-! ## Hurwitz decomposition -/

def U (x y z : ℝ) : ℝ := sp x y z * sq x y z - 9 * sr x y z

def F0 (ρ : ℝ) (x y z : ℝ) : ℝ :=
  e3 ρ * sr x y z * (e2 ρ * sp x y z * sq x y z - e3 ρ * sr x y z)

def F1 (ρ h x y z : ℝ) : ℝ :=
  let p := sp x y z; let q := sq x y z; let r := sr x y z
  e2 ρ * e3 ρ * h * q * r + e2 ρ * m3 ρ h * p * q ^ 2 + e3 ρ * m2 h * p ^ 2 * r
    - 2 * e3 ρ * m3 ρ h * q * r - m4 ρ h * p ^ 2 * r

def F2 (ρ h x y z : ℝ) : ℝ :=
  let p := sp x y z; let q := sq x y z; let r := sr x y z
  e2 ρ * h * m3 ρ h * q ^ 2 + e3 ρ * h * m2 h * p * r - 2 * h * m4 ρ h * p * r
    + m2 h * m3 ρ h * p ^ 2 * q - m3 ρ h ^ 2 * q ^ 2

def Psi2 (ρ h x y z : ℝ) : ℝ :=
  let p := sp x y z; let q := sq x y z; let r := sr x y z
  e2 ρ * e3 ρ * h ^ 2 * q * r + 2 * e2 ρ * h * m3 ρ h * p * q ^ 2
    - 9 * e2 ρ * h * m3 ρ h * q * r + 2 * e3 ρ * h * m2 h * p ^ 2 * r
    - e3 ρ * h * m3 ρ h * q * r - 3 * h * m4 ρ h * p ^ 2 * r
    + m2 h * m3 ρ h * p ^ 3 * q - m3 ρ h ^ 2 * p * q ^ 2

theorem delta3_decomposition (ρ h x y z v : ℝ) :
    hurwitzDelta (c1 ρ h x y z v) (c2 ρ h x y z v) (c3 ρ h x y z v) (c4 ρ h x y z v) =
      F0 ρ x y z + F1 ρ h x y z * v + F2 ρ h x y z * v ^ 2
        + h * (m2 h * m3 ρ h * U x y z + Kf ρ h * sr x y z) * v ^ 3 := by
  unfold hurwitzDelta c1 c2 c3 c4 F0 F1 F2 U Kf
  ring

theorem psi_decomposition (ρ h x y z v : ℝ) :
    c1 ρ h x y z v * (F0 ρ x y z + F1 ρ h x y z * v + F2 ρ h x y z * v ^ 2)
        - k2 ρ * h * sr x y z * v * c3 ρ h x y z v =
      sp x y z * F0 ρ x y z
        + (sp x y z * F1 ρ h x y z + h * e2 ρ * e3 ρ * sr x y z * U x y z) * v
        + Psi2 ρ h x y z * v ^ 2 + h * F2 ρ h x y z * v ^ 3 := by
  unfold c1 c3 F0 F1 F2 Psi2 U k2 e2 e3
  ring

end

end DStabilityHardness
