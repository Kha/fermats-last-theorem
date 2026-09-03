import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open scoped TensorProduct

theorem AutomorphicForm.exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A]
    (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) :
    ∃ t x : GL (Fin 2) (L ⊗[K] A),
      t ∈ Subgroup.centralizer
          ({AutomorphicForm.toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) ∧
      AutomorphicForm.normString K L A σ t = AutomorphicForm.toTensorGL K L A γ ∧
      t = x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime.solution
