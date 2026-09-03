import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin
    (R : Type u) [CommRing R] (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]

    (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (F' : Type u) [Field F'] [Algebra R F'] (j' : F') [Fact (j' ≠ 0)]

    {L : Type v} [Field L] [Algebra K L] {L' : Type v} [Field L'] [Algebra K L']
    (ι : ↥(chartAlgFin R F j) → L) (ι' : ↥(chartAlgFin R F' j') → L')

    (C₁ : CurveModel K L)
    (e₁ : C₁.C ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₁]
    (he₁ : e₁ ≫ pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C₁.toBase)
    (hne₁ : Nonempty (Scheme.Opens.toScheme
      ((e₁ ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤))))
    (pin₁ : ∀ a : ↥(chartAlgFin R F j),
      C₁.ffEquiv.symm
        (C₁.C.germToFunctionField
          ((e₁ ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤))
          (((e₁ ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ιFin R F j) ''ᵁ ⊤)).hom
            (((ιFin R F j).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv a)))) = ι a)

    (C₂ : CurveModel K L')
    (e₂ : C₂.C ⟶ pullback (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₂]
    (he₂ : e₂ ≫ pullback.snd (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C₂.toBase)
    (hne₂ : Nonempty (Scheme.Opens.toScheme
      ((e₂ ≫ pullback.fst (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ιFin R F' j') ''ᵁ ⊤))))
    (pin₂ : ∀ b : ↥(chartAlgFin R F' j'),
      C₂.ffEquiv.symm
        (C₂.C.germToFunctionField
          ((e₂ ≫ pullback.fst (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ιFin R F' j') ''ᵁ ⊤))
          (((e₂ ≫ pullback.fst (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ιFin R F' j') ''ᵁ ⊤)).hom
            (((ιFin R F' j').appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F' j'))).inv b)))) = ι' b)

    (πX : AlgebraicCurve.TwoChartIntegralModel R F' j' ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    (hπX : πX ≫ toBase R F j = toBase R F' j')
    (θ : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j'))
    (hchart : ιFin R F' j' ≫ πX = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ ιFin R F j)

    (Φ : L →ₐ[K] L') (hΦθ : ∀ a : ↥(chartAlgFin R F j), Φ (ι a) = ι' (θ a))
    (hint : Φ.toRingHom.IsIntegral) (hfin : FiniteAlong K Φ)

    (y : {q : Spec (CommRingCat.of K) ⟶ C₂.C // q ≫ C₂.toBase = 𝟙 _})
    (x : {q : Spec (CommRingCat.of K) ⟶ C₁.C // q ≫ C₁.toBase = 𝟙 _})
    (hyx : x.1 ≫ e₁ ≫ pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      y.1 ≫ e₂ ≫ pullback.fst (toBase R F' j') (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ πX) :
    C₁.pointEquivPlace x = (C₂.pointEquivPlace y).restrictAlong Φ hint := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin.solution
