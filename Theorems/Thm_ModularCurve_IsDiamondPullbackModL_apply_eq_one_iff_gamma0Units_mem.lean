import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL
import P2M.Util
import P2M.Sol.S_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem

set_option autoImplicit false

open scoped MatrixGroups in

theorem ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem
    {K : Type*} [Field K] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    {ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))}
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ) (γ : CongruenceSubgroup.Gamma0 M) :
    ρ γ = 1 ↔ CohCarrier.gamma0Units M γ ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsDiamondPullbackModL_apply_eq_one_iff_gamma0Units_mem.solution
