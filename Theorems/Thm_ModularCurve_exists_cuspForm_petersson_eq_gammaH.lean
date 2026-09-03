import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_cuspForm_petersson_eq_gammaH

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_petersson_eq_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)) :
    ∃ f : CuspForm (CohCarrier.GammaH M H) 2,
      ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = ℓ g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_cuspForm_petersson_eq_gammaH.solution
