import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelRelabelling_relabel_smul_variableChange
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

set_option autoImplicit false

open scoped Classical in

theorem ModularCurve.LevelRelabelling.relabel_smul_variableChange
    {T : Type} [Field T] (W : WeierstrassCurve T) [W.IsElliptic] (C : WeierstrassCurve.VariableChange T)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T)
    (hP : W.toAffine.Equation D.xP D.yP) (hQ : W.toAffine.Equation D.xQ D.yQ)

    (h₁ : g 0 0 • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + g 1 0 • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ ≠ 0)
    (h₂ : g 0 1 • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + g 1 1 • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ ≠ 0) :
    ModularCurve.LevelRelabelling.LevelPData.relabel (C • W) g (D.variableChange C) =
      (ModularCurve.LevelRelabelling.LevelPData.relabel W g D).variableChange C := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelRelabelling_relabel_smul_variableChange.solution
