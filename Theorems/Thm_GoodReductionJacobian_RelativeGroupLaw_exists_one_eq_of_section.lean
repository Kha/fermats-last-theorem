import Mathlib
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_of_section
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    ∃ L' : RelativeGroupLaw R f, L'.one (𝟙 _) = e ∧ (L.IsCommutative → L'.IsCommutative) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_section.solution
