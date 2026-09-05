module

public import Definitions.Def_ModularCurve_LevelOneProlongationPair
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair

@[expose] public section
attribute [-simp] ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong
open AlgebraicCurve IsLocalRing ModularCurve
set_option synthInstance.maxHeartbeats 400000 in
theorem ModularCurve.PlaceSpecialization.exists_levelOneProlongationPair
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    Nonempty (P.LevelOneProlongationPair) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair.solution
