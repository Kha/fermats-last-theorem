import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_maximalIdeal_eq_span_map_of_forall_exists_sub_mem

set_option autoImplicit false

open IsLocalRing

theorem IsDiscreteValuationRing.exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_maximalIdeal_eq_span_map_of_forall_exists_sub_mem
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (σ : A →+* W) (hσ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (hres : ∀ w : W, ∃ a : A, w - σ a ∈ IsLocalRing.maximalIdeal W) :
    ∃ ρ : W ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A,
      ∀ a : A, ρ (σ a) = algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_maximalIdeal_eq_span_map_of_forall_exists_sub_mem.solution
