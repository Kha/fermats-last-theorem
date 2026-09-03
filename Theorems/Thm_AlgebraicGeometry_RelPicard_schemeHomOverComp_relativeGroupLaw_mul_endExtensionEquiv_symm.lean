import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian open AlgebraicGeometry.RelPicard hiding baseChange_relativeGroupLaw_mul_compat

set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.RelPicard.schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsSeparated D.toBase]
    (hN : NeronModelPropertyBundle R K D.toBase)
    (h' : RepresentsRelSubPic (baseChange R c K) (sectionBaseChange K ε)
      (algEquivZeroCut (baseChange R c K) (sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
    (φη : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase)
    (hhom : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver s (D.baseChange K).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη)) :
    ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y)
          (hN.endExtensionEquiv.symm φη) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
          (NeronModelInfra.schemeHomOverComp x (hN.endExtensionEquiv.symm φη))
          (NeronModelInfra.schemeHomOverComp y (hN.endExtensionEquiv.symm φη)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm.solution
