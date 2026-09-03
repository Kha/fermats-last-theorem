import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_grpObj_eq

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : WeierstrassProjModel.RelativeGroupLaw R f) :
    ∃ g : GrpObj (Over.mk f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (lift a b ≫ g.mul) =
          G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        overHomToSchemeHomOver (toUnit (Over.mk t) ≫ g.one) = G.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (a ≫ g.inv) = G.inv t (overHomToSchemeHomOver a)) :=
  let G' : GoodReductionJacobian.RelativeGroupLaw R f :=
    { mul := G.mul, one := G.one, inv := G.inv,
      mul_assoc := G.mul_assoc, one_mul := G.one_mul, mul_one := G.mul_one,
      inv_mul_cancel := G.inv_mul_cancel,
      mul_natural := G.mul_natural }
  ⟨G'.grpObjOverMk, fun t a b => G'.overHomToSchemeHomOver_mul t a b,
    fun t => G'.overHomToSchemeHomOver_one t, fun t a => G'.overHomToSchemeHomOver_inv t a⟩
