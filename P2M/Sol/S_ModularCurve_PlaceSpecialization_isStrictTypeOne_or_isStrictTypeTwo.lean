import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularNodes
import P2M.Util
namespace P2MW.S_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hW : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W))
      ≠ P.redFst W) :
    P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W := by
  rcases P.d1 W with h | h
  ·
    right
    have h' : P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) := h
    refine ⟨h', fun h2 => hW ?_⟩
    rw [h', h2]
  ·
    left
    exact ⟨h, hW⟩
