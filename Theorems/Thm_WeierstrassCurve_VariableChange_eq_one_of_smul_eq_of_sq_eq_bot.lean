import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_sq_eq_bot

set_option autoImplicit false

universe u

theorem WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_sq_eq_bot
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (I : Ideal T) (hI : I ^ 2 = ⊥) (C : WeierstrassCurve.VariableChange T)
    (hu : (C.u : T) - 1 ∈ I) (hr : C.r ∈ I) (hs : C.s ∈ I) (ht : C.t ∈ I)
    (hC : C • W = W) : C = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_sq_eq_bot.solution
