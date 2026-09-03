import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_subfieldClosure_range_germToFunctionField_union_range_eq_top
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve
universe u

theorem AlgebraicCurve.TwoChartIntegralModel.subfieldClosure_range_germToFunctionField_union_range_eq_top
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (S : Type u) [CommRing S] [Algebra R S]
    [hint : IsIntegral (pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S))))]
    (x : ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))))
    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)))] :
    Subfield.closure
      (Set.range (fun a : ↥(TwoChartIntegralModel.chartAlgFin R F j) =>
        ((pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).germToFunctionField
            ((pullback.fst (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
            (((pullback.fst (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).app
                ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv a))))) ∪
        Set.range (fun s : S =>
          algebraMap ((pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).presheaf.stalk x)
            (pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).functionField
            (((pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).presheaf.germ ⊤ x trivial).hom
              (((pullback.snd (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))))) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_subfieldClosure_range_germToFunctionField_union_range_eq_top.solution
