import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hαint : αH.toRingHom.IsIntegral)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hne₀ : Nonempty (Scheme.Opens.toScheme ((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤))))
    (hpin₀ : haveI := hne₀
      ∀ a : ↥(chartAlgFin p (XHDRLevel.ΓN p M H hpM) hj),
            ((Meta₀.ffEquiv.symm
                (Meta₀.C.germToFunctionField
                  ((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤))
                  (((eeta₀ ≫ pullback.fst (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app ((ιFin p (XHDRLevel.ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                    (((ιFin p (XHDRLevel.ΓN p M H hpM) hj).appIso ⊤).inv
                      ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (XHDRLevel.ΓN p M H hpM) hj))).inv a))))
                : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) =
              coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (XHDRLevel.ΓN p M H hpM))) : LaurentSeries ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    [IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)] [IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]

    [IsFinite (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))]
    [Flat (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))]
    [LocallyOfFinitePresentation (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))]

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hw₀ : Place.ramificationIndexAlong αH (𝔛.Meta.pointEquivPlace y) = 1)
    (k : ℕ) (y' : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (e : Fin k → ℕ)
    (hinj : Function.Injective y') (hne : ∀ j, y' j ≠ y)
    (hfib : ∀ j, (𝔛.Meta.pointEquivPlace (y' j)).restrictAlong αH hαint = (𝔛.Meta.pointEquivPlace y).restrictAlong αH hαint)
    (hall : ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      w.restrictAlong αH hαint = (𝔛.Meta.pointEquivPlace y).restrictAlong αH hαint → w ≠ 𝔛.Meta.pointEquivPlace y →
        ∃ j, w = 𝔛.Meta.pointEquivPlace (y' j))
    (he : ∀ j, e j = Place.ramificationIndexAlong αH (𝔛.Meta.pointEquivPlace (y' j))) :

    (∀ j, (y' j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1) ∧

    (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) ((y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ 𝔛.π.1)
        (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
        (by rw [Category.assoc, 𝔛.π.2, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta,
              ← Category.assoc, y.2, Category.id_comp])).I.comap
        (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) =
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
          (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
          (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2, Category.id_comp])).I *
        ∏ j, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ((y' j).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
            (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
            (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, (y' j).2,
                  Category.id_comp])).I ^ (e j) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_comap_curveChange_pi_ofPoint_genericFibre_eq_mul_prod_pow_of_restrictAlong_pointEquivPlace_eq.solution
