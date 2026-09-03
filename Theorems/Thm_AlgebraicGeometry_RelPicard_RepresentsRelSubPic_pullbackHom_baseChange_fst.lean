import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_baseChange_fst
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hR : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hPR : Nonempty (hR.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (hR' : RepresentsRelSubPic (baseChange R c' R') (sectionBaseChange R' ε')
      (algEquivZeroCut (baseChange R c' R') (sectionBaseChange R' ε')) (D'.baseChange R'))
    (hPR' : Nonempty (hR'.poincare.L ≅ (BaseChange.ofR c' ε' R'
      (h'.poincare.pullbackAlong ⟨pullback.fst D'.toBase (specMap R R'), pullback.condition⟩)).L))
    (hf' : curveChange f hf (specMap R R') ≫ baseChange R c R' = baseChange R c' R')
    (hεbc : (sectionBaseChange R' ε').1 ≫ curveChange f hf (specMap R R') = (sectionBaseChange R' ε).1) :
    (RepresentsRelSubPic.pullbackHom (curveChange f hf (specMap R R')) hf' hεbc hR hR').1 ≫
        pullback.fst D'.toBase (specMap R R') =
      pullback.fst D.toBase (specMap R R') ≫ (RepresentsRelSubPic.pullbackHom f hf hε h h').1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst.solution
