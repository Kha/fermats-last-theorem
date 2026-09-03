import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_IsDiamondPullbackModL_apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0

set_option autoImplicit false

theorem ModularCurve.IsDiamondPullbackModL.apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    {ρ : CongruenceSubgroup.Gamma0 N →*
        (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')))}
    (hρ : ModularCurve.IsDiamondPullbackModL K N H' ρ)
    (γ : CongruenceSubgroup.Gamma0 N) (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')))
    (hx : (x : LaurentSeries K) ∈ ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 N)) :
    ρ γ x = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsDiamondPullbackModL_apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0.solution
