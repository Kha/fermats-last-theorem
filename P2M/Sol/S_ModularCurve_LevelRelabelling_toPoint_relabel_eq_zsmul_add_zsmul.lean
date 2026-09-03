import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
namespace P2MW.S_ModularCurve_LevelRelabelling_toPoint_relabel_eq_zsmul_add_zsmul

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling
open scoped Classical

theorem solution
    {T : Type u} [Field T] (W : WeierstrassCurve T) (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T)
    (hP : g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ ≠ 0)
    (hQ : g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ ≠ 0) :
    toPoint W (LevelPData.relabel W g D).xP (LevelPData.relabel W g D).yP =
        g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ ∧
      toPoint W (LevelPData.relabel W g D).xQ (LevelPData.relabel W g D).yQ =
        g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ := by
  classical

  have key : ∀ R : W.toAffine.Point, R ≠ 0 → toPoint W (ofPoint W R).1 (ofPoint W R).2 = R := by
    intro R hR
    rcases R with _ | ⟨x, y, h⟩
    · exact absurd rfl hR
    · show toPoint W x y = _
      rw [toPoint, dif_pos h]
  constructor
  · exact key _ hP
  · exact key _ hQ
