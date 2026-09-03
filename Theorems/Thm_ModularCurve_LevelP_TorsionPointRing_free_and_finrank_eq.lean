import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq

set_option autoImplicit false

universe u

theorem ModularCurve.LevelP.TorsionPointRing.free_and_finrank_eq
    {B : Type u} [CommRing B] [Nontrivial B] (W : WeierstrassCurve B) {p : ℕ} (hp : Odd p)
    (hp1 : p ≠ 1) (hpu : IsUnit (p : B)) :
    Module.Free B (ModularCurve.LevelP.TorsionPointRing W p) ∧
      Module.finrank B (ModularCurve.LevelP.TorsionPointRing W p) = p ^ 2 - 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq.solution
