import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected
    {C X : Scheme.{0}} [ConnectedSpace X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut C)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : C, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (U : C.Opens) (hUcl : IsClosed (U : Set C)) (hUconn : _root_.IsConnected (U : Set C))
    (G₀ : Subgroup G) (hG₀ : ∀ g : G, g ∈ G₀ ↔ (ρ g).hom ⁻¹ᵁ U = U) :
    ∃ ρ₀ : G₀ →* Aut (U : Scheme.{0}),
      (∀ g : G₀, (ρ₀ g).hom ≫ U.ι = U.ι ≫ (ρ (g : G)).hom) ∧
      (∃ hπ₀ : ∀ g : G₀, (ρ₀ g).hom ≫ (U.ι ≫ π) = U.ι ≫ π,
        IsFinite (U.ι ≫ π) ∧
        Function.Surjective (U.ι ≫ π).base ∧
        (∀ u u' : (U : Scheme.{0}), (U.ι ≫ π).base u = (U.ι ≫ π).base u' ↔ ∃ g : G₀, (ρ₀ g).hom.base u = u') ∧
        (∀ V : X.Opens, Function.Injective ((U.ι ≫ π).app V)) ∧
        (∀ V : X.Opens, Set.range ((U.ι ≫ π).app V) =
          {s | ∀ g : G₀, (ρ₀ g).hom.appLE ((U.ι ≫ π) ⁻¹ᵁ V) ((U.ι ≫ π) ⁻¹ᵁ V)
            (by rw [← Scheme.Hom.comp_preimage, hπ₀ g]) s = s})) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.solution
