import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (A : Type u) [CommRing A] [Algebra R A] :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    let tε := Scheme.TwoAffineOpenCover.specMap R (DualNumber A)
    let t₀ := Scheme.TwoAffineOpenCover.specMap R A
    (∀ x y : SchemeHomOver tε D.toBase,
        dualNumberReduction R A ≫ x.1 = (L.one t₀).1 → dualNumberReduction R A ≫ y.1 = (L.one t₀).1 →
          dualNumberReduction R A ≫ (L.mul tε x y).1 = (L.one t₀).1) ∧
    (∀ (φ : SchemeHomOver D.toBase D.toBase),
        (∀ {T : Scheme.{u}} (s : T ⟶ Spec (.of R)) (x y : SchemeHomOver s D.toBase),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) →
        ∀ x : SchemeHomOver tε D.toBase, dualNumberReduction R A ≫ x.1 = (L.one t₀).1 →
          dualNumberReduction R A ≫ (x.1 ≫ φ.1) = (L.one t₀).1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem.solution
