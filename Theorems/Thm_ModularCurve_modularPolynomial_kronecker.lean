module

public import Definitions.Def_ModularCurve_X0
public import Mathlib.Algebra.Polynomial.Eval.Defs
import P2M.Util
import P2M.Sol.S_ModularCurve_modularPolynomial_kronecker

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one

open ModularCurve
theorem ModularCurve.modularPolynomial_kronecker (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (data : ModularPolynomialData ℓ) : data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) = (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularPolynomial_kronecker.solution
