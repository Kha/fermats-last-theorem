import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm

set_option autoImplicit false

open NumberField

theorem NumberField.InfiniteAdeleRing.norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm
    (K : Type) [Field K] [NumberField K] (x : K) :
    (∀ v : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) x v‖ = v x) ∧
    ∏ v : InfinitePlace K, v x ^ v.mult = ‖algebraMap K (InfiniteAdeleRing K) x‖ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm.solution
