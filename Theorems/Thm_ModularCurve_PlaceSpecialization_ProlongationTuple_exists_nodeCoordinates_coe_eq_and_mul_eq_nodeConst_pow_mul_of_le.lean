import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_coe_eq_and_mul_eq_nodeConst_pow_mul_of_le

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeCoordinates_coe_eq_and_mul_eq_nodeConst_pow_mul_of_le
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N))
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK' : K ≤ K')
    (c : R.NodeCoordinates K w) (ϖ : ↥(NodeLocalized.coeffSubring A K)) (E : ℕ)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (ϖ' : ↥(NodeLocalized.coeffSubring A K')) (r : ℕ) (u₀ : ↥(NodeLocalized.coeffSubring A K')) (hu₀ : IsUnit u₀)
    (hϖ : (ϖ : AlgebraicClosure ℚ) = ((ϖ' ^ r * u₀ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ)) :
    ∃ (c' : R.NodeCoordinates K' w) (uK' : ↥(R.nodeIntegersOver K' w)), IsUnit uK' ∧
      ((uK' : ↥(modularFunctionFieldBar (N * q))) = u) ∧
      ((c'.x : ↥(modularFunctionFieldBar (N * q))) = c.x) ∧ ((c'.y : ↥(modularFunctionFieldBar (N * q))) = c.y) ∧
      IsUnit (R.nodeConst K' w u₀ ^ E * uK') ∧
      c'.x * c'.y = R.nodeConst K' w ϖ' ^ (r * E) * (R.nodeConst K' w u₀ ^ E * uK') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_coe_eq_and_mul_eq_nodeConst_pow_mul_of_le.solution
