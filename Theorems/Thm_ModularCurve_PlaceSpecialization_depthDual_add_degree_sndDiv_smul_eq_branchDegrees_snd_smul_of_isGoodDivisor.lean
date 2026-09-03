import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_depthDual_add_degree_sndDiv_smul_eq_branchDegrees_snd_smul_of_isGoodDivisor

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.depthDual_add_degree_sndDiv_smul_eq_branchDegrees_snd_smul_of_isGoodDivisor
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (g : SemilinearAut k (modularFunctionFieldC k 1))
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w ∈ W, frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr w) = w)
    (e : Place k (modularFunctionFieldC k 1) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ)
    (s₀ : ↥(nodePairsOfPlaces g W))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hgood : P.IsGoodDivisor D) :
    P.depthDual g W depth D +
        Divisor.degree (P.sndDiv D) •
          ((((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ)) •
            crossingCoord s₀) =
      (P.branchDegrees D).2 •
        ((((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ)) •
          crossingCoord s₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_depthDual_add_degree_sndDiv_smul_eq_branchDegrees_snd_smul_of_isGoodDivisor.solution
