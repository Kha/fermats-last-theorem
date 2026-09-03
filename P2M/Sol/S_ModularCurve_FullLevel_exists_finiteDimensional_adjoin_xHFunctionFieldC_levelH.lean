import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import P2M.Util
namespace P2MW.S_ModularCurve_FullLevel_exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH
attribute [-simp] ModularCurve.qExpandAlgHomC_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ t : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      FiniteDimensional ↥(IntermediateField.adjoin (ResidueField A) ({t} : Set ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := by
  haveI : IsAlgClosed (ResidueField ↥A) := inferInstance
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex := inferInstance
  obtain ⟨x, -, -, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A)
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (translation_mem_GammaH (q ^ 2 * M') (levelH q M'))
  exact ⟨x, hfd⟩
