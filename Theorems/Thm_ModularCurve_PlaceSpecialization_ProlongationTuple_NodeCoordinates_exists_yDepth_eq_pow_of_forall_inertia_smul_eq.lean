import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_yDepth_eq_pow_of_forall_inertia_smul_eq
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.exists_yDepth_eq_pow_of_forall_inertia_smul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
    {K : IntermediateField ℚ (AlgebraicClosure ℚ)} {w : Place k (modularFunctionFieldC k N)}
    (c : R.NodeCoordinates K w) (hVI : R.ValueIntegralityLaw w)
    (hK : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K, σ z = z)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0)
    (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (hVrat : V.IsRational)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) :
    ∃ d : ℕ, c.yDepth V = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_yDepth_eq_pow_of_forall_inertia_smul_eq.solution
