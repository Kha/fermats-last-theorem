import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : maximalIdeal W = Ideal.span {ϖ})
    (R : Type) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Finite (ResidueField R)]
    (κ : W →+* R) [IsLocalHom κ]
    (θ : R →+* R) (hres : ∀ r : R, θ r - r ∈ maximalIdeal R) (hfix : θ (κ ϖ) = κ ϖ) :
    θ.comp κ = κ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span.solution
