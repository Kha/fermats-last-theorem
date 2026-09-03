import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPQuotient
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelP_quotientByLine_variableChange

set_option autoImplicit false

universe u

theorem ModularCurve.LevelP.quotientByLine_variableChange
    {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ) (C : WeierstrassCurve.VariableChange A)
    {x : A} (h : ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit ((W.ΨSq a).eval x)) :
    ModularCurve.LevelP.quotientByLine (C • W) p (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r)) =
      C • ModularCurve.LevelP.quotientByLine W p x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelP_quotientByLine_variableChange.solution
