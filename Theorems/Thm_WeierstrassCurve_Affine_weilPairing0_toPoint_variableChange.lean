import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.Affine

theorem WeierstrassCurve.Affine.weilPairing0_toPoint_variableChange
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (C : WeierstrassCurve.VariableChange K) [(C • W).IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    weilPairing0 (C • W) K (ℓ : ℤ)
        (toPoint ((C • W).baseChange K) (D.variableChange C).xP (D.variableChange C).yP)
        (toPoint ((C • W).baseChange K) (D.variableChange C).xQ (D.variableChange C).yQ) =
      weilPairing0 W K (ℓ : ℤ) (toPoint (W.baseChange K) D.xP D.yP) (toPoint (W.baseChange K) D.xQ D.yQ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange.solution
