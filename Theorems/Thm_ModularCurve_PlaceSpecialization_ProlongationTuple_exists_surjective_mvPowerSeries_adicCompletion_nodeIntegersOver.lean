import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_surjective_mvPowerSeries_adicCompletion_nodeIntegersOver
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_surjective_mvPowerSeries_adicCompletion_nodeIntegersOver
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o)) :
    ∃ (θW : (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ}) →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
      (θ : MvPowerSeries (Fin 2) (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ}) →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)),
      (∀ o : ↥(NodeLocalized.coeffSubring A K), θW (Ideal.Quotient.mk _ (PowerSeries.C o)) = algebraMap _ _ (R.nodeConst K w o)) ∧
      θW (Ideal.Quotient.mk _ PowerSeries.X) = algebraMap _ _ (R.nodeConst K w ϖ) ∧
      Function.Surjective θ ∧
      θ.comp MvPowerSeries.C = θW ∧
      θ (MvPowerSeries.X 0) = algebraMap _ _ c.x ∧
      θ (MvPowerSeries.X 1) = algebraMap _ _ c.y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_surjective_mvPowerSeries_adicCompletion_nodeIntegersOver.solution
