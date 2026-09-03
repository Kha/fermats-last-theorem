import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import P2M.Util
import P2M.Sol.S_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
attribute [-instance] AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel Topology

theorem AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
    (F : Type) [Field F] [NumberField F]
    {X : Type*} [TopologicalSpace X] (U : Set X) (_hU : IsOpen U)
    (χ₁ χ₂ : X → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
    (_hχ₁ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₁ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (_hχ₂ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₂ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (f : X → AdelicGL2 (𝓞 F) F → ℂ)
    (_hf : ∀ x ∈ U, IsInducedSection (𝓞 F) F (χ₁ x) (χ₂ x) (f x))
    (_hfK : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2)
      (U ×ˢ {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact.solution
