import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_morphismRestrict

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_restrict_action_quotient_clauses_morphismRestrict
    {M X : Scheme.{u}} (G : Type u) [Group G] [Finite G] (ρ : G →* Aut M)
    (π : M ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (U : X.Opens) :
    ∃ ρ' : G →* Aut ((π ⁻¹ᵁ U : M.Opens) : Scheme.{u}),
      (∀ g : G, (ρ' g).hom ≫ (π ⁻¹ᵁ U).ι = (π ⁻¹ᵁ U).ι ≫ (ρ g).hom) ∧
      (∃ hπ' : ∀ g : G, (ρ' g).hom ≫ (π ∣_ U) = π ∣_ U,
        IsFinite (π ∣_ U) ∧
        Function.Surjective (π ∣_ U).base ∧
        (∀ u u' : ((π ⁻¹ᵁ U : M.Opens) : Scheme.{u}), (π ∣_ U).base u = (π ∣_ U).base u' ↔ ∃ g : G, (ρ' g).hom.base u = u') ∧
        (∀ V : (U : Scheme.{u}).Opens, Function.Injective ((π ∣_ U).app V)) ∧
        (∀ V : (U : Scheme.{u}).Opens, Set.range ((π ∣_ U).app V) =
          {s | ∀ g : G, (ρ' g).hom.appLE ((π ∣_ U) ⁻¹ᵁ V) ((π ∣_ U) ⁻¹ᵁ V)
            (by rw [← Scheme.Hom.comp_preimage, hπ' g]) s = s})) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_morphismRestrict.solution
