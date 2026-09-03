import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_x1FunctionFieldC_qExpFunctionFieldC_gammaH_bot_coe_eq

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_algEquiv_x1FunctionFieldC_qExpFunctionFieldC_gammaH_bot_coe_eq
    (k : Type*) [Field k] (M : ℕ) [NeZero M] :
    ∃ e : ↥(x1FunctionFieldC k M) ≃ₐ[k] ↥(qExpFunctionFieldC k (CohCarrier.GammaH M ⊥)),
      ∀ x : ↥(x1FunctionFieldC k M),
        ((e x : ↥(qExpFunctionFieldC k (CohCarrier.GammaH M ⊥))) : LaurentSeries k) = (x : LaurentSeries k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_x1FunctionFieldC_qExpFunctionFieldC_gammaH_bot_coe_eq.solution
