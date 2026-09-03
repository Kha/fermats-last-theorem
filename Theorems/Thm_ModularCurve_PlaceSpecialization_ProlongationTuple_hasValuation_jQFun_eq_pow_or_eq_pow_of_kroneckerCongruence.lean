import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_PlaceDepth
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hqA : A.valuation (q : AlgebraicClosure ℚ) < 1)
    {N : ℕ} [NeZero N] {data : ModularPolynomialData q} (hKr : KroneckerCongruence q data)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {γ γ' : A.ValueGroup} (hγ' : 1 < γ')
    (hj : W.HasValuation A (jFun N q) γ) (hjq : W.HasValuation A (jQFun N q) γ') :
    γ' = γ ^ q ∨ γ = γ' ^ q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence.solution
