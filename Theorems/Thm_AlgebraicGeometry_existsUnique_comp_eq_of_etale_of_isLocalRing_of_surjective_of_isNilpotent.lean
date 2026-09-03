import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p]
    {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (π : B →+* C) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (Q : Spec (CommRingCat.of B) ⟶ Y) (a₀ : Spec (CommRingCat.of C) ⟶ X)
    (h : a₀ ≫ p = Spec.map (CommRingCat.ofHom π) ≫ Q) :
    ∃! Q' : Spec (CommRingCat.of B) ⟶ X, Q' ≫ p = Q ∧ Spec.map (CommRingCat.ofHom π) ≫ Q' = a₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent.solution
