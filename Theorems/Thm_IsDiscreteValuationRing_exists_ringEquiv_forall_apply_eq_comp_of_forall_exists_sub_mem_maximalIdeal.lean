import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem IsDiscreteValuationRing.exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal
    (A W₀ W S : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀] [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    [CommRing S] (I : Ideal S) [IsHausdorff I S]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (σ₀ : A →+* W₀) (hσ₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ})
    (hres₀ : ∀ w : W₀, ∃ a : A, w - σ₀ a ∈ IsLocalRing.maximalIdeal W₀)
    (σ : A →+* W) (hσ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (hres : ∀ w : W, ∃ a : A, w - σ a ∈ IsLocalRing.maximalIdeal W)
    (C₀ : W₀ →+* S) (C : W →+* S)
    (hC₀ : ∀ w ∈ IsLocalRing.maximalIdeal W₀, C₀ w ∈ I) (hC : ∀ w ∈ IsLocalRing.maximalIdeal W, C w ∈ I)
    (h : ∀ a : A, C₀ (σ₀ a) = C (σ a)) :
    ∃ βW : W₀ ≃+* W, (∀ w : W₀, C₀ w = C (βW w)) ∧ (∀ a : A, βW (σ₀ a) = σ a) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal.solution
