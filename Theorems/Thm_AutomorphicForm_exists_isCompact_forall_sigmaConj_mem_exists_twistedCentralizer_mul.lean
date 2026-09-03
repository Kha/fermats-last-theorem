import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open NumberField IsDedekindDomain TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (S : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hS : IsCompact S) :
    ∃ Ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact Ω ∧
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∈ S →
          ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∃ d ∈ Ω, x = t * d := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul.solution
