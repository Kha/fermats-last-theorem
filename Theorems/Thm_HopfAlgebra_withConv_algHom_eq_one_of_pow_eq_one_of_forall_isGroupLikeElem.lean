import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem

set_option autoImplicit false

universe u v

theorem HopfAlgebra.withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem
    (k : Type u) [Field k] [IsAlgClosed k] (H : Type v) [CommRing H] [HopfAlgebra k H]
    [Coalgebra.IsCocomm k H]
    (φ : WithConv (H →ₐ[k] k)) (m : ℕ) (hm : (m : k) ≠ 0) (hφ : φ ^ m = 1)
    (h1 : ∀ g : H, IsGroupLikeElem k g → φ g = 1) :
    φ = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem.solution
