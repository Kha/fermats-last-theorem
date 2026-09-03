import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularNodes
import P2M.Util
namespace P2MW.S_ModularCurve_PlaceSpecialization_not_isStrictTypeOne_and_isStrictTypeTwo
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    ¬ (P.IsStrictTypeOne W ∧ P.IsStrictTypeTwo W) := by
  rintro ⟨⟨h1, -⟩, ⟨h2, h2'⟩⟩

  apply h2'
  have h2e : P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) := h2
  rw [← h2e]
  exact h1
