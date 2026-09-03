import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_opens_comp_eq_base_eq_of_isLocalHom
    {X Y Y' : Scheme.{u}} (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (z : X) (hzU : z ∈ U)
    [X.IsGermInjectiveAt z]
    (β : Y' ⟶ Y) [LocallyOfFiniteType β]
    {O : Type u} [CommRing O] [IsLocalRing O]
    (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y) (ℓ : Spec (CommRingCat.of O) ⟶ Y') (hℓ : ℓ ≫ β = ℓ₀)
    (φ : CommRingCat.of O ⟶ X.presheaf.stalk z) [IsLocalHom φ.hom]
    (hφ : Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α) :
    ∃ (U' : X.Opens) (hU' : U' ≤ U) (hzU' : z ∈ U') (α' : (U' : Scheme.{u}) ⟶ Y'),
      α' ≫ β = X.homOfLE hU' ≫ α ∧ α'.base ⟨z, hzU'⟩ = ℓ.base (IsLocalRing.closedPoint O) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom.solution
