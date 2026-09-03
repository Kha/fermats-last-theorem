import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-simp] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve TensorProduct

theorem AlgebraicGeometry.RelEffCartierDiv.nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R))))
    (r r' d : ℕ) {W : Scheme.{u}} (w : W ⟶ pullback c (𝟙 (Spec (CommRingCat.of R)))) [IsClosedImmersion w]
    [IsFinite (w ≫ pullback.snd c (𝟙 _))] [Flat (w ≫ pullback.snd c (𝟙 _))] [Etale (w ≫ pullback.snd c (𝟙 _))]
    (hEI : E.I = (sectionIdeal c ε (𝟙 _)) ^ r * w.ker ^ r')
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R))
    (q : Fin d → {p : Spec (CommRingCat.of Ω) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _})
    (hqinj : Function.Injective (fun m => (q m).1))
    (hqW : ∀ m, ∃ y : Spec (CommRingCat.of Ω) ⟶ W, (q m).1 ≫ mapOnProdOver c s (Category.comp_id s) = y ≫ w)
    (hqall : ∀ y : Spec (CommRingCat.of Ω) ⟶ W, y ≫ w ≫ pullback.snd c (𝟙 _) = s →
      ∃ m, (q m).1 ≫ mapOnProdOver c s (Category.comp_id s) = y ≫ w)
    (pε : {p : Spec (CommRingCat.of Ω) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _})
    (hpε : pε.1 ≫ pullback.fst c s = s ≫ ε.1) :
    Nonempty ((E.pullbackAlong s (Category.comp_id s)).lineBundle ≅
      ((pε.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_lineBundle_pullbackAlong_iso_invModule_pow_ker_mul_pow_prod_ker.solution
