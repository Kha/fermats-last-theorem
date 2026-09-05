module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_Place_ord_eq_zero_of_isIntegral_adjoin

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Place.ord_eq_zero_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring) (hx : IsIntegral (Algebra.adjoin K {j}) x) (hx' : IsIntegral (Algebra.adjoin K {j}) x⁻¹) : v.ord x = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_eq_zero_of_isIntegral_adjoin.solution
