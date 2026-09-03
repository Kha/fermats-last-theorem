import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_valuationSubring_gaussType_unramified_laurentBaseChange_xHFunctionField

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.exists_valuationSubring_gaussType_unramified_laurentBaseChange_xHFunctionField
    (A : ValuationSubring (AlgebraicClosure ℚ))

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})

    (N : ℕ) (H : Subgroup (ZMod N)ˣ)
    (K'' : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK'' : K'' = ModularCurve.laurentBaseChange ↥k₀ (ModularCurve.xHFunctionField N H))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K''] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K'']
    (j'' : ↥K'') (hj'' : ((j'' : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) :
    ∃ V : ValuationSubring ↥K'',
      (∀ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K'' r ∈ V) ∧
      algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K'' ⟨π₀, hπ⟩ ∈ V.nonunits ∧
      (∀ P : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ¬ (Polynomial.C (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∣ P) →
        Polynomial.aeval j'' P ∈ V ∧ (Polynomial.aeval j'' P)⁻¹ ∈ V) ∧
      (∀ f : ↥K'', f ∈ V.nonunits → f * (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K'' ⟨π₀, hπ⟩)⁻¹ ∈ V) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_valuationSubring_gaussType_unramified_laurentBaseChange_xHFunctionField.solution
