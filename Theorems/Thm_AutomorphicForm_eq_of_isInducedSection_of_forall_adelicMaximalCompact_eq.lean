import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm~exists_mem_adelicBorel_mul_eq"

theorem AutomorphicForm.eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
    (K : Type) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ₁ φ₂ : AdelicGL2 (𝓞 K) K → ℂ)
    (h₁ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ₁) (h₂ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ₂)
    (h : ∀ k : adelicMaximalCompact K, φ₁ (k : AdelicGL2 (𝓞 K) K) = φ₂ (k : AdelicGL2 (𝓞 K) K)) :
    φ₁ = φ₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq.solution
