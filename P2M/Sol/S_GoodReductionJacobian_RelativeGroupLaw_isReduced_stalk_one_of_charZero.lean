import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one
import Theorems.Thm_IsLocalRing_isReduced_of_forall_exists_derivation_of_charZero
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_stalk_one_of_charZero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (k : Type) [Field k] [CharZero k] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    _root_.IsReduced (G.presheaf.stalk ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k))) := by
  set e : ↥G := (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k) with he
  letI alg : Algebra k (G.presheaf.stalk e) :=
    ((G.presheaf.germ ⊤ e trivial).hom.comp (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
  obtain ⟨hk, hder⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one k g L
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian g
  exact IsLocalRing.isReduced_of_forall_exists_derivation_of_charZero k (G.presheaf.stalk e) hk hder
