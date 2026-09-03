import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_exists_ord_sub_pow_sq_eq_one_of_ord_jqModC
set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_ord_jqModC
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hj : w.ord ((⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N))
        - (⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)) ^ (q ^ 2)) = 1)
    (hjφ : (arithFrobC q k N • w).ord ((⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N))
        - (⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N)) ^ (q ^ 2)) = 1) :
    ∃ (g₀ : LaurentSeries ℚ) (y : LaurentSeries ↥A) (g : ↥(modularFunctionFieldBar N))
      (gbar : ↥(modularFunctionFieldC k N)),
      g₀ ∈ modularFunctionFieldFull N ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) g₀ ∧
      coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) g₀ ∧
      (gbar : LaurentSeries k) = coeffMap red y ∧
      w.ord (gbar - gbar ^ (q ^ 2)) = 1 ∧ (arithFrobC q k N • w).ord (gbar - gbar ^ (q ^ 2)) = 1 ∧
      ∀ U : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        (P.sp U = w ∨ frobOnPlacesGeomLevel k N data hKr (P.sp U) = w ∨
            P.sp U = frobOnPlacesGeomLevel k N data hKr w) →
          g ∈ U.toValuationSubring := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_ord_sub_pow_sq_eq_one_of_ord_jqModC.solution
