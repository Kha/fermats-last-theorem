import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_map_eq_of_comap_eq

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_map_eq_of_comap_eq {K F K' F' : Type*}
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    (τ : K →+* K') (φ : F →+* F') (hφ : ∀ c : K, φ (algebraMap K F c) = algebraMap K' F' (τ c))
    (v : Place K F) (v' : Place K' F') (h : v'.toValuationSubring.comap φ = v.toValuationSubring)
    (hv : v.IsRational) {x : F} (hx : x ∈ v.toValuationSubring) :
    v'.evalAt (φ x) = τ (v.evalAt x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_evalAt_map_eq_of_comap_eq.solution
