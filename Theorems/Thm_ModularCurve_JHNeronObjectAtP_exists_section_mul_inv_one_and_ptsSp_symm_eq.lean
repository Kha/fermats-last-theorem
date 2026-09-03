import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_ModularCurve_XHDiamondModL
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_exists_section_mul_inv_one_and_ptsSp_symm_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_section_mul_inv_one_and_ptsSp_symm_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) :

    (∀ (x y : JH M H) (s t : NeronModelInfra.SchemeHomOver Λ.σA O.g),
      (O.pts x).1 = barPt A ≫ s.1 → (O.pts y).1 = barPt A ≫ t.1 →
        (O.pts (x + y)).1 = barPt A ≫ (O.L.mul Λ.σA s t).1 ∧
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.mul Λ.σA s t)) =
          O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) +
            O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ t)) ∧

    (∀ (x : JH M H) (s : NeronModelInfra.SchemeHomOver Λ.σA O.g),
      (O.pts x).1 = barPt A ≫ s.1 →
        (O.pts (-x)).1 = barPt A ≫ (O.L.inv Λ.σA s).1 ∧
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.inv Λ.σA s)) =
          - O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s)) ∧

    ((O.pts 0).1 = barPt A ≫ (O.L.one Λ.σA).1 ∧
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.one Λ.σA)) = 0) ∧

    (∀ s : NeronModelInfra.SchemeHomOver Λ.σA O.g,
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) = 0 ↔
        resPt A ≫ s.1 = (resPt A ≫ Λ.σA) ≫ (O.L.one (𝟙 (base p))).1) ∧

    (∀ s t : NeronModelInfra.SchemeHomOver Λ.σA O.g, barPt A ≫ s.1 = barPt A ≫ t.1 → s = t) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_section_mul_inv_one_and_ptsSp_symm_eq.solution
