import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash

set_option autoImplicit false
open scoped MatrixGroups ModularForm TensorProduct

theorem ModularCurve.periodMapOf_gammaH_eq_comp_of_coe_eq_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (α : GL (Fin 2) ℝ)
    (hα : 0 < ((Matrix.GeneralLinearGroup.det α : ℝˣ) : ℝ))
    (c : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
    (hc : ∀ δ : ↥(CohCarrier.GammaH M H),
      (((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) = α * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * α⁻¹)
    (f g : CuspForm (CohCarrier.GammaH M H) 2) (hg : ⇑g = ⇑f ∣[(2 : ℤ)] α) :
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f).comp (MonoidHom.toAdditive c) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash.solution
