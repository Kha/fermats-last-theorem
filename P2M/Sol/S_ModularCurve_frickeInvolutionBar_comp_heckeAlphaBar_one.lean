module

public import Mathlib
public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_CuspidalClass
public import Definitions.Def_ModularCurve_AtkinLehnerPartial
public import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
public import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
public import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace Ws14Fricke

theorem isAtkinLehnerAutFull_one_of_isFrickeAutFull (q : ℕ) [NeZero q]
    {σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q)}
    (hσ : IsFrickeAutFull (1 * q) σ) : IsAtkinLehnerAutFull 1 q σ := by
  intro d _ hd
  obtain rfl : d = 1 := Nat.dvd_one.mp hd
  exact ⟨hσ 1 (1 * q) (one_mul _) inferInstance inferInstance,
    hσ (1 * q) 1 (mul_one _) inferInstance inferInstance⟩

theorem isAtkinLehnerAutFull_one_frickeInvolutionFull (q : ℕ) [NeZero q] :
    IsAtkinLehnerAutFull 1 q (frickeInvolutionFull (1 * q)) :=
  isAtkinLehnerAutFull_one_of_isFrickeAutFull q
    (isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q)))
end Ws14Fricke

theorem solution (q : ℕ) [NeZero q] :
    (frickeInvolutionBar (1 * q)).toAlgHom.comp (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
      = heckeBetaBar (AlgebraicClosure ℚ) 1 q :=
  (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) 1 q (frickeInvolutionFull (1 * q))
    (Ws14Fricke.isAtkinLehnerAutFull_one_frickeInvolutionFull q)).1
