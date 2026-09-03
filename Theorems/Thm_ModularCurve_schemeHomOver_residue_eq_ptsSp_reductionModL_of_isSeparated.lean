import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated
open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory NeronModelInfra IsLocalRing
theorem ModularCurve.schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated
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
      = (ptsSp (reductionModL B p x)).1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated.solution
