import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isDomain

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Hom.exists_lift_schemeTheoreticImage_of_isDomain
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {A : Type u} [CommRing A] [IsDomain A] (u : Spec (CommRingCat.of A) ⟶ Y)
    (h : u.base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Set.range f.base) :
    ∃ v : Spec (CommRingCat.of A) ⟶ f.image, v ≫ f.imageι = u := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isDomain.solution
