import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (σ : CongruenceSubgroup.Gamma0 M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ⇑f ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) :
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      CohCarrier.diamondRaw M H ℂ σ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash.solution
