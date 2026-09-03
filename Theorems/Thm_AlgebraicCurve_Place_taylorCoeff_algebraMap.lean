import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_taylorCoeff_algebraMap

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place Polynomial

theorem AlgebraicCurve.Place.taylorCoeff_algebraMap
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t : F) (c : K) (n : ℕ) :
    taylorCoeff v t n (algebraMap K F c) = if n = 0 then c else 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_taylorCoeff_algebraMap.solution
