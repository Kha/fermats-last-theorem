import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_taylorRem_smul

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorRem_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) (r : ℕ) :
    taylorRem v t (c • f) r = c • taylorRem v t f r := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_taylorRem_smul.solution
