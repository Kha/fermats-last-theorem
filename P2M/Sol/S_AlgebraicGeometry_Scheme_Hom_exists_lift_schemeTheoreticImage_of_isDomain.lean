import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isReduced
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isDomain

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {A : Type u} [CommRing A] [IsDomain A] (u : Spec (CommRingCat.of A) ⟶ Y)
    (h : u.base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Set.range f.base) :
    ∃ v : Spec (CommRingCat.of A) ⟶ f.image, v ≫ f.imageι = u := by
  apply AlgebraicGeometry.Scheme.Hom.exists_lift_schemeTheoreticImage_of_isReduced f u

  rintro _ ⟨x, rfl⟩
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ⤳ x :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  have hux : u.base ⟨⊥, Ideal.isPrime_bot⟩ ⤳ u.base x := hgen.map u.base.hom.continuous
  rw [specializes_iff_mem_closure] at hux
  exact closure_mono (Set.singleton_subset_iff.mpr h) hux
