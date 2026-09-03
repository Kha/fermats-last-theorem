import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ)
    (φ : ModularCurve.Period.parabolicHoms (ZMod n) Γ (ZMod n))
    (hφ : ∀ γ : Γ, IsOfFinOrder γ → (φ : Additive Γ →+ ZMod n) (Additive.ofMul γ) = 0) :
    ∃ x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ,
      (Int.castAddHom (ZMod n)).comp (x : Additive Γ →+ ℤ) = (φ : Additive Γ →+ ZMod n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.solution
