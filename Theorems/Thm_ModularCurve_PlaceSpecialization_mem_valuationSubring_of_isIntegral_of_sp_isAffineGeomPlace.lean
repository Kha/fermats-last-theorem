import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_mem_valuationSubring_of_isIntegral_of_sp_isAffineGeomPlace
set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.mem_valuationSubring_of_isIntegral_of_sp_isAffineGeomPlace
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (g : ↥(modularFunctionFieldBar N))
    (hint : IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) g)
    (U : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hU : IsAffineGeomPlace k N (P.sp U)) : g ∈ U.toValuationSubring := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_mem_valuationSubring_of_isIntegral_of_sp_isAffineGeomPlace.solution
