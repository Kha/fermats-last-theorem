import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelRelabelling_toPoint_relabel_eq_zsmul_add_zsmul

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling
open scoped Classical

theorem ModularCurve.LevelRelabelling.toPoint_relabel_eq_zsmul_add_zsmul
    {T : Type u} [Field T] (W : WeierstrassCurve T) (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T)
    (hP : g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ ≠ 0)
    (hQ : g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ ≠ 0) :
    toPoint W (LevelPData.relabel W g D).xP (LevelPData.relabel W g D).yP =
        g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ ∧
      toPoint W (LevelPData.relabel W g D).xQ (LevelPData.relabel W g D).yQ =
        g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelRelabelling_toPoint_relabel_eq_zsmul_add_zsmul.solution
