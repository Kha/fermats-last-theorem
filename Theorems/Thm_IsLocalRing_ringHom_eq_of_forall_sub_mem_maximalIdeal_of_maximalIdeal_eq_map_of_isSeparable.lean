import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_ringHom_eq_of_forall_sub_mem_maximalIdeal_of_maximalIdeal_eq_map_of_isSeparable

set_option autoImplicit false

universe u v w

theorem IsLocalRing.ringHom_eq_of_forall_sub_mem_maximalIdeal_of_maximalIdeal_eq_map_of_isSeparable
    (A₀ : Type u) (W₀ : Type v) (C : Type w)
    [CommRing A₀] [IsLocalRing A₀] [CommRing W₀] [HenselianLocalRing W₀]
    [Algebra A₀ W₀] [IsLocalHom (algebraMap A₀ W₀)]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ W₀))
    [FiniteDimensional (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField W₀)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField W₀)]
    [CommRing C] [IsLocalRing C] [IsHausdorff (IsLocalRing.maximalIdeal C) C]
    (u₁ u₂ : W₀ →+* C) [IsLocalHom u₁]
    (hA₀ : u₁.comp (algebraMap A₀ W₀) = u₂.comp (algebraMap A₀ W₀))
    (h : ∀ w : W₀, u₁ w - u₂ w ∈ IsLocalRing.maximalIdeal C) :
    u₁ = u₂ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_ringHom_eq_of_forall_sub_mem_maximalIdeal_of_maximalIdeal_eq_map_of_isSeparable.solution
