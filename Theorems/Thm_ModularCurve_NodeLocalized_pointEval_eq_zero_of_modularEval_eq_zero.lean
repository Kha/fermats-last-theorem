module

public import Mathlib
public import Definitions.Def_ModularCurve_NodeLocalized
public import Definitions.Def_ModularCurve_NodeDescent
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized
theorem ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (s : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs : modularEval (1 * q) (coeffSubring A K) s = 0) :
    pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero.solution
