import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_isPullback_of_isArtinianRing
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing NeronModelInfra GoodReductionJacobian"

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_isPullback_of_isArtinianRing
    {R : Type u} [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    {k₀ : Type u} [Field k₀] (π : R →+* k₀) (hπ : Function.Surjective π)
    {A A' A₀ : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [IsProper f] [Flat f]
    {f' : A' ⟶ Spec (CommRingCat.of R)} (L' : RelativeGroupLaw R f')
    {f₀ : A₀ ⟶ Spec (CommRingCat.of k₀)} (hf₀ : Function.Bijective f₀.appTop)
    (i : A₀ ⟶ A) (hi : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom π)))
    (s : Spec (CommRingCat.of R) ⟶ A) (hs : s ≫ f = 𝟙 _)
    (e₁ e₂ : A ⟶ A') (he₁ : e₁ ≫ f' = f) (he₂ : e₂ ≫ f' = f)
    (h : i ≫ e₁ = i ≫ e₂) (hs' : s ≫ e₁ = s ≫ e₂) : e₁ = e₂ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_isPullback_of_isArtinianRing.solution
