import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_LevelRaising_parabolicHoms_castAddHom_comp_eq_zero_iff

set_option autoImplicit false
theorem LevelRaising.parabolicHoms_castAddHom_comp_eq_zero_iff
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} {p : ℕ}
    (x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) :
    (Int.castAddHom (ZMod p)).comp (x : Additive Γ →+ ℤ) = 0
      ↔ ∃ x' : ModularCurve.Period.parabolicHoms ℤ Γ ℤ, x = (p : ℤ) • x' := by p2m_exact_reverting @_root_.P2MW.S_LevelRaising_parabolicHoms_castAddHom_comp_eq_zero_iff.solution
