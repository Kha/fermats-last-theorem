import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_eq_diamondPullbackModL_of_forall_coe_mem_gamma0_apply_eq

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups
universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_eq_diamondPullbackModL_of_forall_coe_mem_gamma0_apply_eq
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (ρ : CongruenceSubgroup.Gamma0 M →*
        (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
          qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ)
    (hfix : ∀ (H : Subgroup (ZMod M)ˣ) (y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
        (y : LaurentSeries K) ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) ↔
          ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ y = y)
    (σ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))
    (hσ : ∀ y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
        (y : LaurentSeries K) ∈ qExpFunctionFieldC K (CohCarrier.GammaH M ⊤) → σ y = y) :
    ∃ γ : CongruenceSubgroup.Gamma0 M, σ = ρ γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_eq_diamondPullbackModL_of_forall_coe_mem_gamma0_apply_eq.solution
