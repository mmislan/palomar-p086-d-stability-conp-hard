module

public import proofs.DStabilityHardness.Certificates

@[expose] public section

/-! Symmetric reduction: the ordered certificates imply nonnegativity for all nonnegative rates. -/

namespace DStabilityHardness

noncomputable section

theorem sp_12 (x y z : ℝ) : sp x y z = sp y x z := by unfold sp; ring
theorem sq_12 (x y z : ℝ) : sq x y z = sq y x z := by unfold sq; ring
theorem sr_12 (x y z : ℝ) : sr x y z = sr y x z := by unfold sr; ring
theorem sp_23 (x y z : ℝ) : sp x y z = sp x z y := by unfold sp; ring
theorem sq_23 (x y z : ℝ) : sq x y z = sq x z y := by unfold sq; ring
theorem sr_23 (x y z : ℝ) : sr x y z = sr x z y := by unfold sr; ring

/-- Nonnegativity of a symmetric function of three nonnegative reals follows from the ordered case. -/
theorem sym_nonneg (P : ℝ → ℝ → ℝ → ℝ) (h12 : ∀ x y z, P x y z = P y x z)
    (h23 : ∀ x y z, P x y z = P x z y)
    (hord : ∀ A B C : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ C → 0 ≤ P (A + B + C) (B + C) C) :
    ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → 0 ≤ P x y z := by
  have hsorted : ∀ x y z : ℝ, z ≤ y → y ≤ x → 0 ≤ z → 0 ≤ P x y z := by
    intro x y z hzy hyx hz
    have := hord (x - y) (y - z) z (by linarith) (by linarith) hz
    have e1 : x - y + (y - z) + z = x := by ring
    have e2 : y - z + z = y := by ring
    rwa [e1, e2] at this
  intro x y z hx hy hz
  rcases le_total y x with hxy | hxy <;> rcases le_total z y with hyz | hyz <;>
    rcases le_total z x with hxz | hxz
  · exact hsorted x y z hyz hxy hz
  · exact hsorted x y z hyz hxy hz
  · rw [h23]; exact hsorted x z y hyz hxz hy
  · rw [h23, h12]; exact hsorted z x y hxy hxz hy
  · rw [h12]; exact hsorted y x z hxz hxy hz
  · rw [h12, h23]; exact hsorted y z x hxz hyz hx
  · exact hsorted x y z (le_trans hxz hxy) (le_trans hyz hxz) hz
  · rw [h12, h23, h12]; exact hsorted z y x hxy hyz hx

theorem F1_nonneg {ρ h x y z : ℝ} (hρ0 : 17 / 10 ≤ ρ) (hρ1 : ρ ≤ 7 / 4) (hh0 : 3 ≤ h) (hh1 : h ≤ 5)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 ≤ F1 ρ h x y z :=
  sym_nonneg (F1 ρ h) (fun x y z => by unfold F1; rw [sp_12, sq_12, sr_12]) (fun x y z => by unfold F1; rw [sp_23, sq_23, sr_23])
    (fun A B C hA hB hC => F1_ordered_nonneg ρ h A B C hρ0 hρ1 hh0 hh1 hA hB hC) x y z hx hy hz

theorem F2_nonneg {ρ h x y z : ℝ} (hρ0 : 17 / 10 ≤ ρ) (hρ1 : ρ ≤ 7 / 4) (hh0 : 3 ≤ h) (hh1 : h ≤ 5)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 ≤ F2 ρ h x y z :=
  sym_nonneg (F2 ρ h) (fun x y z => by unfold F2; rw [sp_12, sq_12, sr_12]) (fun x y z => by unfold F2; rw [sp_23, sq_23, sr_23])
    (fun A B C hA hB hC => F2_ordered_nonneg ρ h A B C hρ0 hρ1 hh0 hh1 hA hB hC) x y z hx hy hz

theorem Psi2_nonneg {ρ h x y z : ℝ} (hρ0 : 17 / 10 ≤ ρ) (hρ1 : ρ ≤ 7 / 4) (hh0 : 3 ≤ h)
    (hh1 : h ≤ 5) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 ≤ Psi2 ρ h x y z :=
  sym_nonneg (Psi2 ρ h) (fun x y z => by unfold Psi2; rw [sp_12, sq_12, sr_12])
    (fun x y z => by unfold Psi2; rw [sp_23, sq_23, sr_23])
    (fun A B C hA hB hC => Psi2_ordered_nonneg ρ h A B C hρ0 hρ1 hh0 hh1 hA hB hC) x y z hx hy hz

end

end DStabilityHardness
