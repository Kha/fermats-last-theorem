import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_quadraticRelation_apply_mem_of_conj_mul_of_eq_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem Representation.quadraticRelation_apply_mem_of_conj_mul_of_eq_zero
    {R : Type} [CommRing R] {Y : Type} [AddCommGroup Y] [Module R Y]
    {G : Type} [Group G] {U : Type} [CommGroup U]
    (ρ : G →* Module.End R Y) (t : G → R) (c : G →* Rˣ) (χ : G →* U) (D : U →* Module.End R Y)
    (ht : ∀ g h : G, t (g * h * g⁻¹) = t h)
    (hD : ∀ (u : U) (g : G), D u * ρ g = ρ g * D u)
    (N : Submodule R Y) (hNρ : ∀ (g : G), ∀ y ∈ N, ρ g y ∈ N) (hND : ∀ (u : U), ∀ y ∈ N, D u y ∈ N)
    (H : Subgroup G)
    (hρH : ∀ (g : G), ∀ h ∈ H, ∀ y : Y, ρ (g * h) y - ρ g y ∈ N)
    (htH : ∀ (g : G), ∀ h ∈ H, ∀ y : Y, (t (g * h) - t g) • y ∈ N)
    (hcH : ∀ (g : G), ∀ h ∈ H, ∀ y : Y, (((c (g * h) : Rˣ) : R) - ((c g : Rˣ) : R)) • y ∈ N)
    (hχH : ∀ (g : G), ∀ h ∈ H, χ (g * h) = χ g)
    (τ : G) (hτ : ρ τ * ρ τ - t τ • ρ τ + ((c τ : Rˣ) : R) • D (χ τ) = 0)
    (g : G) (h : G) (hh : h ∈ H) (y : Y) :
    (ρ (g * τ * g⁻¹ * h) * ρ (g * τ * g⁻¹ * h) - t (g * τ * g⁻¹ * h) • ρ (g * τ * g⁻¹ * h)
      + ((c (g * τ * g⁻¹ * h) : Rˣ) : R) • D (χ (g * τ * g⁻¹ * h))) y ∈ N := by p2m_exact_reverting @_root_.P2MW.S_Representation_quadraticRelation_apply_mem_of_conj_mul_of_eq_zero.solution
