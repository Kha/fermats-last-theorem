import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_finEmbed_globalPoints_diag_mul_heckeGenAt_inv_mem_levelOne_rat
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SiegelCoordinates
  IsDedekindDomain

theorem NumberField.AdelicLevel.finEmbed_globalPoints_diag_mul_heckeGenAt_inv_mem_levelOne_rat
    (L : Ideal (𝓞 ℚ)) (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (ϖ : (v.adicCompletion ℚ)ˣ) (hϖ : (ϖ : v.adicCompletion ℚ) = algebraMap ℚ _ (p : ℚ)) :
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperUnit (p : ℚ) 0 1 (Nat.cast_ne_zero.mpr hp.ne_zero) one_ne_zero)))
        * (heckeGenAt (𝓞 ℚ) ℚ v ϖ)⁻¹ ∈ levelOne (𝓞 ℚ) ℚ L ⊓ finiteAdelicGL2Subgroup ℚ ∧
    (heckeGenAt (𝓞 ℚ) ℚ v ϖ)⁻¹
        * AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
          (upperUnit (p : ℚ) 0 1 (Nat.cast_ne_zero.mpr hp.ne_zero) one_ne_zero)))
      ∈ levelOne (𝓞 ℚ) ℚ L ⊓ finiteAdelicGL2Subgroup ℚ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_finEmbed_globalPoints_diag_mul_heckeGenAt_inv_mem_levelOne_rat.solution
