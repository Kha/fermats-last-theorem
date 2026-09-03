import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
    {B₁ B₀ : Type} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π) (hI : RingHom.ker π ≤ IsLocalRing.maximalIdeal B₁)
    {X X₀ : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of B₁)) (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X)
    (hg : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom π))
    (h₁ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom)
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom)
    (s : Γ(X₀, ⊤)) (hs : IsUnit s) :
    ∃ u : Γ(X, ⊤), IsUnit u ∧ g.appTop.hom u = s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal.solution
