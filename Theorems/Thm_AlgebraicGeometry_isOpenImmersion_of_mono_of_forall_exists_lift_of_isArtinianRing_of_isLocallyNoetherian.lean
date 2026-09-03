import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing IsLocalRing"

universe u

theorem AlgebraicGeometry.isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian
    {X M : Scheme.{u}} [IsLocallyNoetherian X] (ϖ : M ⟶ X) [LocallyOfFinitePresentation ϖ] [Mono ϖ]
    (h : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ X) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    IsOpenImmersion ϖ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian.solution
