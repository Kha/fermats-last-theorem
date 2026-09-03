import Mathlib
import Theorems.Thm_CuspForm_exists_gamma0_eleven_apply_eq_eta_sq_mul_eta_sq
import P2M.Util
namespace P2MW.S_CuspForm_exists_ne_zero_gamma0_eleven
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem solution : ∃ f : CuspForm (CongruenceSubgroup.Gamma0 11) 2, f ≠ 0 := by
  obtain ⟨f, hf⟩ := CuspForm.exists_gamma0_eleven_apply_eq_eta_sq_mul_eta_sq
  refine ⟨f, fun hzero => ?_⟩
  have hI : ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet :=
    UpperHalfPlane.I.2
  have h11 : (11 : ℂ) * ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by
    show 0 < ((11 : ℂ) * ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)).im
    have : ((11 : ℂ) * ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)).im = 11 * (UpperHalfPlane.I : UpperHalfPlane).im := by
      simp [Complex.mul_im]
    rw [this]
    exact mul_pos (by norm_num) UpperHalfPlane.I.im_pos
  have h := hf UpperHalfPlane.I
  rw [hzero] at h
  have hne : ModularForm.eta ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) ^ 2 *
      ModularForm.eta (11 * ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (ModularForm.eta_ne_zero hI)) (pow_ne_zero 2 (ModularForm.eta_ne_zero h11))
  exact hne (by simpa using h.symm)
