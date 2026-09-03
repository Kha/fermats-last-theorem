import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    IsScalarTower ℝ (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) ∧
    Module.Finite ℝ (InfiniteAdeleRing K) ∧ Module.Finite ℝ (L ⊗[K] InfiniteAdeleRing K) ∧
    Continuous (algebraMap ℝ (InfiniteAdeleRing K)) ∧
    ContinuousSMul ℝ (L ⊗[K] InfiniteAdeleRing K) ∧
    Continuous (Algebra.norm ℝ : L ⊗[K] InfiniteAdeleRing K → ℝ) ∧
    Continuous (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => Algebra.norm ℝ X.det) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det.solution
