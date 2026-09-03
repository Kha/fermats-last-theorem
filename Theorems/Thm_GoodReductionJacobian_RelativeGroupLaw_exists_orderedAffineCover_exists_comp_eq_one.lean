import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_exists_comp_eq_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
theorem GoodReductionJacobian.RelativeGroupLaw.exists_orderedAffineCover_exists_comp_eq_one
    {B : Type} [CommRing B] [IsLocalRing B] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of B))
    (L : RelativeGroupLaw B f) (hA : AbelianSchemePropertyBundle B f) :
    ∃ (𝒰 : A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)),
      e₀ ≫ (𝒰.U i₀).ι = (L.one (𝟙 _)).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_exists_comp_eq_one.solution
