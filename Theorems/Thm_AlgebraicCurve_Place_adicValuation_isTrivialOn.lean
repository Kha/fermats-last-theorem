module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_Place_adicValuation_isTrivialOn

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Place.adicValuation_isTrivialOn {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsTrivialOn K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isTrivialOn.solution
