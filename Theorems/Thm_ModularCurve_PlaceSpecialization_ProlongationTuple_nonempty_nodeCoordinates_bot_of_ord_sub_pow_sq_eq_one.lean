import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nonempty_nodeCoordinates_bot_of_ord_sub_pow_sq_eq_one
set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.nonempty_nodeCoordinates_bot_of_ord_sub_pow_sq_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    (hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q)) (hGEN : FunctionFieldGeneration (N * q))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (g₀ : LaurentSeries ℚ) (y : LaurentSeries ↥A) (g : ↥(modularFunctionFieldBar N))
    (gbar : ↥(modularFunctionFieldC k N))
    (h₀ : g₀ ∈ modularFunctionFieldFull N)
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) g₀)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) g₀)
    (hgbar : (gbar : LaurentSeries k) = coeffMap red y)
    (hordw : w.ord (gbar - gbar ^ (q ^ 2)) = 1)
    (hordφ : (arithFrobC q k N • w).ord (gbar - gbar ^ (q ^ 2)) = 1)
    (hpole : ∀ U : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (P.sp U = w ∨ frobOnPlacesGeomLevel k N data hKr (P.sp U) = w ∨
          P.sp U = frobOnPlacesGeomLevel k N data hKr w) →
        g ∈ U.toValuationSubring) :
    Nonempty (R.NodeCoordinates (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) w) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nonempty_nodeCoordinates_bot_of_ord_sub_pow_sq_eq_one.solution
