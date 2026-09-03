import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_petersson_eq_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (ℓ : Module.Dual ℂ (CuspForm Γ 2)) :
    ∃ f : CuspForm Γ 2,
      ∀ g : CuspForm Γ 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
          UpperHalfPlane.petersson 2 f g τ) = ℓ g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex.solution
