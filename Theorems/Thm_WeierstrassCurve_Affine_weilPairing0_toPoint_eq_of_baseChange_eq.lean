import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_weilPairing0_toPoint_eq_of_baseChange_eq

set_option autoImplicit false

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.Affine.weilPairing0_toPoint_eq_of_baseChange_eq
    {F₁ F₂ Ω : Type*} [Field F₁] [Field F₂] [Field Ω] [Algebra F₁ Ω] [Algebra F₂ Ω]
    [IsAlgClosed Ω] [DecidableEq Ω]
    (W₁ : WeierstrassCurve F₁) (W₂ : WeierstrassCurve F₂) [W₁.IsElliptic] [W₂.IsElliptic]
    (h : W₁⁄Ω = W₂⁄Ω) (n : ℤ) (x₁ y₁ x₂ y₂ : Ω) :
    ((weilPairing0 W₁ Ω n (toPoint (W₁⁄Ω) x₁ y₁) (toPoint (W₁⁄Ω) x₂ y₂) : Ωˣ) : Ω) =
      ((weilPairing0 W₂ Ω n (toPoint (W₂⁄Ω) x₁ y₁) (toPoint (W₂⁄Ω) x₂ y₂) : Ωˣ) : Ω) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_weilPairing0_toPoint_eq_of_baseChange_eq.solution
