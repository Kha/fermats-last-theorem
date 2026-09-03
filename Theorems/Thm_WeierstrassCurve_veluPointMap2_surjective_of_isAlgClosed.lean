import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.veluPointMap2_surjective_of_isAlgClosed
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) {x₀ y₀ : K} (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    Function.Surjective (veluPointMap2 h2 hQ hgy hΔ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed.solution
