import Mathlib
import P2M.Util
import P2M.Sol.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average

set_option autoImplicit false

open scoped InnerProductSpace

theorem InnerProductSpace.exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average
    {G : Type*} [Group G] {L : Type*} [AddCommGroup L] [Module ℂ L]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : G →* (L →ₗ[ℂ] L)) (S : Submodule ℂ L) (hS : ∀ x : G, ∀ f ∈ S, ρ x f ∈ S)
    (ι : L → H)
    (hι : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → ι (a • f + b • g) = a • ι f + b • ι g)
    (c : G → ℝ) (hc : ∀ x, 0 < c x)
    (hρ : ∀ x : G, ∀ f ∈ S, ‖ι (ρ x f)‖ ^ 2 = c x * ‖ι f‖ ^ 2)
    (P : L → Prop) (E : L → L)
    (hE : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → E (a • f + b • g) = a • E f + b • E g)
    (hEP : ∀ f ∈ S, P (E f))
    (hEinner : ∀ f ∈ S, ∀ g ∈ S, P g → ⟪ι (E f), ι g⟫_ℂ = ⟪ι f, ι g⟫_ℂ)
    (φ φ' : L) (hφ : φ ∈ S) (hPφ : P φ) (hφ' : φ' ∈ S)
    (hspan : ∀ ε : ℝ, 0 < ε →
      ∃ v ∈ Submodule.span ℂ (Set.range fun x : G => ρ x φ), ‖ι φ' - ι v‖ < ε)
    (W : Submodule ℂ L) (hWS : W ≤ S)
    (hWφ' : W ≤ Submodule.span ℂ (Set.range fun x : G => ρ x φ'))
    (hWρ : ∀ x : G, ∀ w ∈ W, ρ x w ∈ W) (hWE : ∀ w ∈ W, E w ∈ W)
    (hEφ' : ∀ x : G, E (ρ x φ') ∈ W) :
    ∀ ε : ℝ, 0 < ε → ∃ w ∈ W, ‖ι φ' - ι w‖ < ε := by p2m_exact_reverting @_root_.P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.solution
