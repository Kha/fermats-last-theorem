import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {ι κ m : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype m] [DecidableEq m]
    (b : Module.Basis ι ℚ K) (x : κ → Matrix m m L) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    (Matrix.of fun p q : ι × κ =>
      Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K)
        (Matrix.trace
          ((x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b p.1)) *
            (x q.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b q.1))))).det =
      ((Algebra.discr ℚ b ^ Fintype.card κ *
          Algebra.norm ℚ (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det : ℚ) : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det.solution
