import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import P2M.Util
namespace P2MW.S_ModularFormClass_qExpansion_heckeU_eq_heckeU

theorem solution {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) :
    UpperHalfPlane.qExpansion 1 (ModularForm.heckeU k p ⇑f)
      = PowerSeries.heckeU p (UpperHalfPlane.qExpansion 1 ⇑f) := by
  ext n
  have h := ModularFormClass.qCoeff_heckeU (k := k) f hΓ hp n
  simp only [ModularFormClass.qCoeff] at h
  rw [PowerSeries.coeff_heckeU, h, ModularForm.coeffHeckeU, mul_comm n p]
  rfl
