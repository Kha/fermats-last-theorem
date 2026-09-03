import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified
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
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (V : (X p (ΓM M H) hj).Opens)
    (hyV : (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ V)
    (hV : FormallyUnramified (V.ι ≫ 𝔛.π.1)) :
    Place.ramificationIndexAlong αH (𝔛.Meta.pointEquivPlace y) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified.solution
