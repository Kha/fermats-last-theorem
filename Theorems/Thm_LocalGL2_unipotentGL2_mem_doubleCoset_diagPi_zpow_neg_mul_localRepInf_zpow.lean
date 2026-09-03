import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow

set_option autoImplicit false

theorem LocalGL2.unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) :
    (∀ b : R, AutomorphicForm.unipotentGL2 (algebraMap R K b) ∈
        HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
          (LocalGL2.diagPi ϖ hϖ0 ^ (0 : ℤ) * LocalGL2.localRepInf ϖ hϖ0 ^ (0 : ℤ))) ∧
    ∀ (u : Rˣ) (r : ℕ),
      AutomorphicForm.unipotentGL2 (algebraMap R K u * ((algebraMap R K ϖ)⁻¹) ^ r) ∈
        HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
          (LocalGL2.diagPi ϖ hϖ0 ^ (-(r : ℤ)) * LocalGL2.localRepInf ϖ hϖ0 ^ (r : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow.solution
