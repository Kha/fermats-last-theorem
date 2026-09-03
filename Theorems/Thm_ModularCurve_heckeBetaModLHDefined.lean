import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeBetaModLHDefined

set_option autoImplicit false

theorem ModularCurve.heckeBetaModLHDefined
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    ModularCurve.HeckeBetaModLHDefined K N H' ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeBetaModLHDefined.solution
