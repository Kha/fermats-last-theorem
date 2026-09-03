import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import P2M.Util
namespace P2MW.S_ModularCurve_schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated

set_option autoImplicit false

open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory NeronModelInfra IsLocalRing

theorem solution
    (p : ℕ) [Fact p.Prime]
    (B : ValuationSubring (AlgebraicClosure ℚ))
    {R : Type} [CommRing R]
    (J : Scheme.{0}) (f : J ⟶ Spec (CommRingCat.of R))
    (hsep : IsSeparated f)
    (σB : Spec (CommRingCat.of ↥B) ⟶ Spec (CommRingCat.of R))
    (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom B.subtype) ≫ σB) f)
    (ptsSp : JZeroC (ResidueField ↥B) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ σB) f)
    (hROPAML : ReductionOfPointsAgreesModL p B f σB ptsA ptsSp)
    (x : JZero p) (P : SchemeHomOver σB f)
    (hgen : Spec.map (CommRingCat.ofHom B.subtype) ≫ P.1 = (ptsA x).1) :
    Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ P.1
      = (ptsSp (reductionModL B p x)).1 := by
  haveI := hsep
  obtain ⟨xA, hg, hs⟩ := hROPAML x
  have hg1 : Spec.map (CommRingCat.ofHom B.subtype) ≫ xA.1 = (ptsA x).1 :=
    congrArg Subtype.val hg
  have hs1 : Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ xA.1
      = (ptsSp (reductionModL B p x)).1 :=
    congrArg Subtype.val hs
  have halg : CommRingCat.ofHom (algebraMap ↥B (AlgebraicClosure ℚ))
      = CommRingCat.ofHom B.subtype := rfl
  have hsq : CommSq (ptsA x).1
      (Spec.map (CommRingCat.ofHom (algebraMap ↥B (AlgebraicClosure ℚ)))) f σB :=
    ⟨by rw [halg]; exact (ptsA x).2⟩
  have hsub : Subsingleton (CommSq.LiftStruct hsq) :=
    (IsSeparated.valuativeCriterion (f := f))
      (⟨↥B, AlgebraicClosure ℚ, (ptsA x).1, σB, hsq⟩ : ValuativeCommSq f)
  have hl : (⟨P.1, by rw [halg]; exact hgen, P.2⟩ : CommSq.LiftStruct hsq)
      = (⟨xA.1, by rw [halg]; exact hg1, xA.2⟩ : CommSq.LiftStruct hsq) :=
    hsub.elim _ _
  have hP1 : P.1 = xA.1 := congrArg CommSq.LiftStruct.l hl
  rw [hP1, hs1]
