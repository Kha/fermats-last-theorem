import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_PowerSeries_FormalHeckeOperators
import P2M.Util
import P2M.Sol.S_ModularFormClass_qExpansion_heckeU_eq_heckeU

theorem ModularFormClass.qExpansion_heckeU_eq_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) :
    UpperHalfPlane.qExpansion 1 (ModularForm.heckeU k p ⇑f)
      = PowerSeries.heckeU p (UpperHalfPlane.qExpansion 1 ⇑f) := by p2m_exact_reverting @_root_.P2MW.S_ModularFormClass_qExpansion_heckeU_eq_heckeU.solution
