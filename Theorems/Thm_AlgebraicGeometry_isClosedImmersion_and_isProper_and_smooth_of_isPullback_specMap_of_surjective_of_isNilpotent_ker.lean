import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker
    {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    (hπs : Function.Surjective π) (hπn : IsNilpotent (RingHom.ker π))
    {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of P)) (f' : X' ⟶ Spec (CommRingCat.of B'))
    (k' : X' ⟶ X) (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π))) :
    (IsClosedImmersion k' ∧ Function.Bijective k'.base) ∧
    (LocallyOfFiniteType f' → LocallyOfFiniteType f) ∧
    (IsProper f' → IsProper f) ∧
    (Flat f → LocallyOfFinitePresentation f → Smooth f' → Smooth f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker.solution
