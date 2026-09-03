import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_localLevelOne_bump_of_forall_apply_diagZ_mul_scalarPi_zpow_eq_ite
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

open IsDedekindDomain NumberField AdelicDock UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.localLevelOne_bump_of_forall_apply_diagZ_mul_scalarPi_zpow_eq_ite
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hfψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      f (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * f g)
    (hfK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → f (g * k) = f g)
    (htorus : ∀ m n : ℤ,
      f (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (m - n) *
          scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n) =
        if m = 0 ∧ n = 0 then 1 else 0) :
    (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), f (h * k) = f h) ∧
    (∀ h : GL (Fin 2) (v.adicCompletion ℚ), f h ≠ 0 →
      ∃ x : v.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        h = AutomorphicForm.unipotentGL2 x * k) ∧
    f 1 = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_localLevelOne_bump_of_forall_apply_diagZ_mul_scalarPi_zpow_eq_ite.solution
