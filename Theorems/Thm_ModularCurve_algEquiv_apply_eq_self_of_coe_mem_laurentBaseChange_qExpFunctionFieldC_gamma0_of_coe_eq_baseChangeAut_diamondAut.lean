import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_qExpFunctionFieldC_gamma0_of_coe_eq_baseChangeAut_diamondAut

set_option autoImplicit false

theorem ModularCurve.algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_qExpFunctionFieldC_gamma0_of_coe_eq_baseChangeAut_diamondAut
    (N : ℕ) [NeZero N]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (d : ℕ) (hd : d.Coprime N)
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut N d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) : LaurentSeries L)) :
    ∀ u : ↥K, (u : LaurentSeries L) ∈
        ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)) →
      θ u = u := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_qExpFunctionFieldC_gamma0_of_coe_eq_baseChangeAut_diamondAut.solution
