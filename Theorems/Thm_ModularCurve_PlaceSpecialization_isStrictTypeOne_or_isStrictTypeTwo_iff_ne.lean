import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne

open AlgebraicCurve ModularCurve
theorem ModularCurve.PlaceSpecialization.isStrictTypeOne_or_isStrictTypeTwo_iff_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W) ↔
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W))
        ≠ P.redFst W := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne.solution
