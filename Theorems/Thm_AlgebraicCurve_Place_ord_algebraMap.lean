module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_Place_ord_algebraMap

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Place.ord_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_algebraMap.solution
