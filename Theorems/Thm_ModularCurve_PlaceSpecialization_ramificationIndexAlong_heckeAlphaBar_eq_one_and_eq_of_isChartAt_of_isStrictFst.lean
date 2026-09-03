import Definitions.Def_ModularCurve_ChartSemicontinuity
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    {v : Place k (modularFunctionFieldC k N)} {S : Set (modularFunctionFieldBar (N * q))}
    (hqN : ¬ q ∣ N) (hS : IsChartAt R v S)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : P.IsStrictFst W) (hWv : P.reduceFst W = v) :
    Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) W = 1 ∧
    ∀ W' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst W' →
      W'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα =
        W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα → W' = W := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst.solution
