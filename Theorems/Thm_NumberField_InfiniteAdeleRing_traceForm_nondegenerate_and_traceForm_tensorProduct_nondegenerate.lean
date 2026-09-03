import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.InfiniteAdeleRing.traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    (Algebra.traceForm ℝ (InfiniteAdeleRing K)).Nondegenerate ∧
      (Algebra.traceForm ℝ (L ⊗[K] InfiniteAdeleRing K)).Nondegenerate := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate.solution
