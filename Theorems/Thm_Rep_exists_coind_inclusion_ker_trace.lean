import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_coind_inclusion_ker_trace

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.exists_coind_inclusion_ker_trace {k G : Type u} [CommRing k] [Group G]
    (U U' : Subgroup G) [U.FiniteIndex] [U'.FiniteIndex] (hUU' : U' ≤ U) (φ : G)
    (X : Rep.{u} k G)
    (ι : X ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
    (ι' : X ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X)) (τ' : Rep.coind U'.subtype (Rep.res U'.subtype X) ⟶ X)
    (hι : ∀ (x : X) (g : G), ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ g x)
    (hτ : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = ∑ᶠ c : G ⧸ U, X.ρ c.out ((y : G → X) (c.out)⁻¹))
    (hι' : ∀ (x : X) (g : G), ((ι'.hom x : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = X.ρ g x)
    (hτ' : ∀ y : Rep.coind U'.subtype (Rep.res U'.subtype X), τ'.hom y = ∑ᶠ c : G ⧸ U', X.ρ c.out ((y : G → X) (c.out)⁻¹))
    {K K' : Rep.{u} k G} (i : K ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (E : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ K) (i' : K' ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X)) (E' : Rep.coind U'.subtype (Rep.res U'.subtype X) ⟶ K')
    (hτi : ∀ y : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom y = 0 ↔ ∃ κ : K, i.hom κ = y)
    (hi' : Function.Injective i'.hom) (hτi' : ∀ y : Rep.coind U'.subtype (Rep.res U'.subtype X), τ'.hom y = 0 ↔ ∃ κ : K', i'.hom κ = y)
    (hE : ∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((i.hom (E.hom y) : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ φ ((y : G → X) (φ⁻¹ * g)) - (y : G → X) g)
    (hE' : ∀ (y : Rep.coind U'.subtype (Rep.res U'.subtype X)) (g : G), ((i'.hom (E'.hom y) : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = X.ρ φ ((y : G → X) (φ⁻¹ * g)) - (y : G → X) g) :
    ∃ (j : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ Rep.coind U'.subtype (Rep.res U'.subtype X)) (jK : K ⟶ K'),
      (∀ (y : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G), ((j.hom y : Rep.coind U'.subtype (Rep.res U'.subtype X)) : G → X) g = (y : G → X) g) ∧
      jK ≫ i' = i ≫ j ∧ ι ≫ j = ι' ∧ E ≫ jK = j ≫ E' ∧ j ≫ τ' = (U'.relIndex U : k) • τ := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_coind_inclusion_ker_trace.solution
