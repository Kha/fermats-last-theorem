import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_algHom_dualNumber_over_counit_schemeHomOver_one_coe_eq_of_torsionSubset_points

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GoodReductionJacobian.RelativeGroupLaw.exists_equiv_algHom_dualNumber_over_counit_schemeHomOver_one_coe_eq_of_torsionSubset_points
    (p : ℕ) [Fact p.Prime]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))}
    (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt p) f)
    (H : Type) [CommRing H] [HopfAlgebra ↥(GaloisRep.ratLocalizedAt p) H]
    (e : ∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T],
      WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T) ≃
        L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) T))) p)
    (hmul : ∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] (φ ψ : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) =
        L.mul _ (e T φ).val (e T ψ).val)
    (hnat : ∀ (T T' : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] [CommRing T'] [Algebra ↥(GaloisRep.ratLocalizedAt p) T']
        (g : T →ₐ[↥(GaloisRep.ratLocalizedAt p)] T') (φ : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
      ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1)
    (k : Type) [Field k] [Algebra ↥(GaloisRep.ratLocalizedAt p) k] [CharP k p] :
    ∃ c : {D : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) =
              algebraMap ↥(GaloisRep.ratLocalizedAt p) k (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H h)} ≃
          {x : SchemeHomOver (Spec.map (CommRingCat.ofHom
              (algebraMap ↥(GaloisRep.ratLocalizedAt p) (DualNumber k)))) f //
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ x.1 =
              (L.one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) k)))).1},
      ∀ D : {D : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) =
              algebraMap ↥(GaloisRep.ratLocalizedAt p) k (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H h)},
        (c D).1 = (e (DualNumber k) D.1).val := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_algHom_dualNumber_over_counit_schemeHomOver_one_coe_eq_of_torsionSubset_points.solution
