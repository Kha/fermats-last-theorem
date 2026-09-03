import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RiemannForm_translation_zero_and_translation_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace Law4YT

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)

theorem comp_base_eq : f ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = f := by
  rw [specMap_algebraMap_self, Category.comp_id]

theorem constPt_eq (x : Pt f) : constPt f x = GoodReductionJacobian.schemeHomOverComp f (comp_base_eq f) x :=
  Subtype.ext rfl

theorem comp_constPt (x y : Pt f) :
    GoodReductionJacobian.schemeHomOverComp (translation f L y) (translation_over f L y) (constPt f x) = constPt f x := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, constPt, ← Category.assoc, translation_over]

theorem comp_idPoint (y : Pt f) :
    GoodReductionJacobian.schemeHomOverComp (translation f L y) (translation_over f L y)
      (RelativeGroupLaw.idPoint : SchemeHomOver f f) = L.mul f RelativeGroupLaw.idPoint (constPt f y) := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.comp_id, translation]

end Law4YT

open Law4YT in
theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (P Q : L.AlgPoints hc k) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)) = 𝟙 A ∧
    translation f L (RelativeGroupLaw.AlgPoints.toPoint (P + Q)) =
      translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q) := by
  constructor
  ·
    rw [RelativeGroupLaw.AlgPoints.toPoint_zero]
    show (L.mul f RelativeGroupLaw.idPoint (constPt f (L.one _))).1 = 𝟙 A
    rw [constPt_eq, L.one_natural, L.mul_one]
  ·
    rw [RelativeGroupLaw.AlgPoints.toPoint_add]

    have hcomp : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q) =
        (GoodReductionJacobian.schemeHomOverComp (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
          (translation_over f L _) (L.mul f RelativeGroupLaw.idPoint (constPt f (RelativeGroupLaw.AlgPoints.toPoint Q)))).1 := by
      rw [GoodReductionJacobian.schemeHomOverComp_coe]; rfl
    rw [hcomp, L.mul_natural, comp_idPoint, comp_constPt, L.mul_assoc]
    show (L.mul f RelativeGroupLaw.idPoint (constPt f (L.mul _ (RelativeGroupLaw.AlgPoints.toPoint P)
      (RelativeGroupLaw.AlgPoints.toPoint Q)))).1 = _
    rw [constPt_eq, L.mul_natural, ← constPt_eq, ← constPt_eq]
