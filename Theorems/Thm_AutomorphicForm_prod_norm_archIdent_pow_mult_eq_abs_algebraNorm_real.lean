import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (z : L ⊗[K] InfiniteAdeleRing K) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    ∏ w : InfinitePlace L, ‖AutomorphicForm.archIdent K L z w‖ ^ w.mult = |Algebra.norm ℝ z| := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real.solution
