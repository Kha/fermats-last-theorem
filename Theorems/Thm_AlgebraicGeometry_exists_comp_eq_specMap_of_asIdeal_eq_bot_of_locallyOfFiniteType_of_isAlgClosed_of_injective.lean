import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed"

theorem AlgebraicGeometry.exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective
    (R : Type) [CommRing R] [IsDomain R]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (x : X) (hx : (f.base x).asIdeal = ⊥)
    (K : Type) [Field K] [IsAlgClosed K] (φ : R →+* K) (hφ : Function.Injective φ) :
    ∃ σ : Spec (CommRingCat.of K) ⟶ X, σ ≫ f = Spec.map (CommRingCat.ofHom φ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_eq_specMap_of_asIdeal_eq_bot_of_locallyOfFiniteType_of_isAlgClosed_of_injective.solution
