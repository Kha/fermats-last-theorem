import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_mem_range_norm_tensorProduct_iff_forall_infinitePlace

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem NumberField.InfiniteAdeleRing.mem_range_norm_tensorProduct_iff_forall_infinitePlace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (a : (InfiniteAdeleRing K)ˣ) :
    ((a : InfiniteAdeleRing K) ∈ Set.range
        (fun t : (L ⊗[K] InfiniteAdeleRing K)ˣ => Algebra.norm (InfiniteAdeleRing K) (t : L ⊗[K] InfiniteAdeleRing K))) ↔
      ∀ w : InfinitePlace K,
        (a : InfiniteAdeleRing K) w ∈ Set.range
          (fun t : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (t : L ⊗[K] w.Completion)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_mem_range_norm_tensorProduct_iff_forall_infinitePlace.solution
