import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel
    {q : ℕ} [Fact q.Prime] (k : Type*) [Field k] [CharP k q] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (v : Place k (modularFunctionFieldC k N)) (hv : IsAffineGeomPlace k N v) :
    IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel.solution
