import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_uniform_iwasawa_mul_of_glFin_eq_one
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

theorem AutomorphicForm.exists_uniform_iwasawa_mul_of_glFin_eq_one
    (K : Type) [Field K] [NumberField K]
    (g : AdelicGL2 (𝓞 K) K) (hg : glFin (𝓞 K) K g = 1) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∃ (ν : AdeleRing (𝓞 K) K) (z b : (AdeleRing (𝓞 K) K)ˣ) (k' : AdelicGL2 (𝓞 K) K),
          ν.2 = 0 ∧ ((z : AdeleRing (𝓞 K) K)).2 = 1 ∧ ((b : AdeleRing (𝓞 K) K)).2 = 1 ∧
          glFin (𝓞 K) K k' = 1 ∧
          (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k'))) ∧
          k * g = unipotentGL2 ν * centralScalar (𝓞 K) K z * diagOne b * k' ∧
          (∀ w : InfinitePlace K, m ≤ ‖((z : AdeleRing (𝓞 K) K)).1 w‖ ∧ ‖((z : AdeleRing (𝓞 K) K)).1 w‖ ≤ M ∧
            m ≤ ‖((b : AdeleRing (𝓞 K) K)).1 w‖ ∧ ‖((b : AdeleRing (𝓞 K) K)).1 w‖ ≤ M) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_uniform_iwasawa_mul_of_glFin_eq_one.solution
