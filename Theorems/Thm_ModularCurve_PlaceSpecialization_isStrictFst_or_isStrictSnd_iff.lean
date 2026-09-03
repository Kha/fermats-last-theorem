import Definitions.Def_ModularCurve_GlueData
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.isStrictFst_or_isStrictSnd_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (P.IsStrictFst W ∨ P.IsStrictSnd W) ↔
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W)) ≠ P.reduceFst W := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff.solution
