import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_section_comp_eq_of_isPullback_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem AlgebraicGeometry.Smooth.exists_section_comp_eq_of_isPullback_of_isNilpotent_ker
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) f₀) :
    ∃ e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f,
      Spec.map (CommRingCat.ofHom π) ≫ e.1 = e₀.1 ≫ g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_section_comp_eq_of_isPullback_of_isNilpotent_ker.solution
