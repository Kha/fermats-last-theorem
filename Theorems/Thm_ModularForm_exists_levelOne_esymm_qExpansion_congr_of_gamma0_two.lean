import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open scoped MatrixGroups

theorem ModularForm.exists_levelOne_esymm_qExpansion_congr_of_gamma0_two (p : ℕ) [Fact p.Prime]
    (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) {B : PowerSeries ℤ}
    (hB : B.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑h) (M : ℤ)
    (hdvd : ∀ n : ℕ, 1 ≤ n → M ∣ B.coeff n) {r : ℕ} (hr : 1 ≤ r) :
    ∃ (F : ModularForm 𝒮ℒ (2 * r)) (T : PowerSeries ℤ),
      T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑F ∧
      (∀ n : ℕ, 1 ≤ n → M ∣ T.coeff n) ∧
      M ∣ PowerSeries.constantCoeff T -
        (-PowerSeries.constantCoeff B) ^ r * ((p.choose r : ℤ) - p * (p.choose (r - 1) : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_levelOne_esymm_qExpansion_congr_of_gamma0_two.solution
