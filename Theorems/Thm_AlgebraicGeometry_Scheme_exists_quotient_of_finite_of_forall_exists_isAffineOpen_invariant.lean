import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant

open AlgebraicGeometry CategoryTheory

universe u v

theorem AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
    {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) :
    ∃ (Y : Scheme.{u}) (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).hom ≫ π = π),
      IsIntegralHom π ∧ IsAffineHom π ∧ Function.Surjective π.base ∧
      (∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x') ∧
      (∀ V : Y.Opens, Function.Injective (π.app V)) ∧
      (∀ V : Y.Opens, Set.range (π.app V) =
        {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s}) ∧
      (∀ U : X.Opens, IsAffineOpen U → (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) →
        ∃ V : Y.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U) ∧
      (∀ (T : Scheme.{u}) (f : X ⟶ T), (∀ g : G, (ρ g).hom ≫ f = f) →
        ∃! f' : Y ⟶ T, π ≫ f' = f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant.solution
