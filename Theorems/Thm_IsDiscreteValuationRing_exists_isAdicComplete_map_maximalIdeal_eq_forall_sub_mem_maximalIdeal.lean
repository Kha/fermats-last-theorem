import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal

set_option autoImplicit false

universe u

theorem IsDiscreteValuationRing.exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W) (_ : IsLocalHom σ),
      Ideal.map σ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal W ∧
      ∀ w : W, ∃ a : A, w - σ a ∈ IsLocalRing.maximalIdeal W := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal.solution
