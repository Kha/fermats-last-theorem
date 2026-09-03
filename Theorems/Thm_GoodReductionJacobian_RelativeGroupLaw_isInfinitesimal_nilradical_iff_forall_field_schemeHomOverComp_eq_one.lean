import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) [IsSeparated f]
    (R : Type) [CommRing R] [Algebra B R] (Q : SchemeHomOver (Scheme.specOver (𝒪 := B) R) f) :
    L.IsInfinitesimal (nilradical R) Q ↔
      ∀ (κ : Type) [Field κ] [Algebra B κ] (φ : R →ₐ[B] κ),
        schemeHomOverComp (Spec.map (CommRingCat.ofHom φ.toRingHom))
          (Scheme.specMap_algHom_comp_specOver φ) Q = L.one (Scheme.specOver (𝒪 := B) κ) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isInfinitesimal_nilradical_iff_forall_field_schemeHomOverComp_eq_one.solution
