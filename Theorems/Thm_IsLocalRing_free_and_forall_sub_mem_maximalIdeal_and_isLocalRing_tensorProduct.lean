import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_free_and_forall_sub_mem_maximalIdeal_and_isLocalRing_tensorProduct

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem IsLocalRing.free_and_forall_sub_mem_maximalIdeal_and_isLocalRing_tensorProduct
    (R : Type u) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (R' : Type u) [CommRing R'] [Algebra R R'] [IsLocalRing R'] [Module.Finite R R'] [Module.Flat R R'] :
    Module.Free R R' ∧ (∀ x : R', ∃ r : R, x - algebraMap R R' r ∈ IsLocalRing.maximalIdeal R') ∧
      IsLocalRing (R' ⊗[R] R') ∧ IsLocalRing ((R' ⊗[R] R') ⊗[R] R') := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_free_and_forall_sub_mem_maximalIdeal_and_isLocalRing_tensorProduct.solution
