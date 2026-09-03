import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_forall_finrank_eq_of_isPullback_of_injective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.forall_finrank_eq_of_isPullback_of_injective
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    {C₀ : Scheme.{0}} (h₀ : C₀ ⟶ Spec (CommRingCat.of R₀)) (hfin : IsFinite h₀) (hfl : Flat h₀)
    (hlfp : LocallyOfFinitePresentation h₀)
    {C : Scheme.{0}} (h : C ⟶ Spec (CommRingCat.of L)) (g : C ⟶ C₀)
    (hg : IsPullback g h h₀ (Spec.map (CommRingCat.ofHom φ)))
    (r : ℕ) (hrank : ∀ x : ↥(Spec (CommRingCat.of L)), h.finrank x = r)
    (t : ↥(Spec (CommRingCat.of R₀))) : h₀.finrank t = r := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_forall_finrank_eq_of_isPullback_of_injective.solution
