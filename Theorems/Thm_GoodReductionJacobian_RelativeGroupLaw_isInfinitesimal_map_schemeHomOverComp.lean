import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_map_schemeHomOverComp

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isInfinitesimal_map_schemeHomOverComp
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {D C : Type} [CommRing D] [Algebra B D] [CommRing C] [Algebra B C] (φ : D →ₐ[B] C)
    (J : Ideal D) (Q : SchemeHomOver (Scheme.specOver (𝒪 := B) D) f) (hQ : L.IsInfinitesimal J Q) :
    L.IsInfinitesimal (J.map φ)
      (schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Scheme.specMap_algHom_comp_specOver φ) Q) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_map_schemeHomOverComp.solution
