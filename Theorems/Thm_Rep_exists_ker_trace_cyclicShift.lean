import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_ker_trace_cyclicShift

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.exists_ker_trace_cyclicShift {k G : Type u} [CommRing k] [Group G]
    (U : Subgroup G) [U.Normal] [U.FiniteIndex] (φ : G) (hφ : ∀ g : G, ∃ (n : ℤ) (u : G), u ∈ U ∧ g = φ ^ n * u)
    (X : Rep.{u} k G)
    (ι : X ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (τ : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ X)
    (hι : ∀ (x : X) (g : G), ((ι.hom x : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ g x)
    (hτ : ∀ f : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom f = ∑ᶠ c : G ⧸ U, X.ρ c.out ((f : G → X) (c.out)⁻¹)) :
    ∃ (K : Rep.{u} k G) (i : K ⟶ Rep.coind U.subtype (Rep.res U.subtype X)) (E : Rep.coind U.subtype (Rep.res U.subtype X) ⟶ K),
      Function.Injective i.hom ∧
      (∀ f : Rep.coind U.subtype (Rep.res U.subtype X), τ.hom f = 0 ↔ ∃ κ : K, i.hom κ = f) ∧
      (∀ (f : Rep.coind U.subtype (Rep.res U.subtype X)) (g : G),
        ((i.hom (E.hom f) : Rep.coind U.subtype (Rep.res U.subtype X)) : G → X) g = X.ρ φ ((f : G → X) (φ⁻¹ * g)) - (f : G → X) g) ∧
      Function.Injective ι.hom ∧ Function.Surjective E.hom ∧
      (∀ f : Rep.coind U.subtype (Rep.res U.subtype X), E.hom f = 0 ↔ ∃ x : X, ι.hom x = f) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_ker_trace_cyclicShift.solution
