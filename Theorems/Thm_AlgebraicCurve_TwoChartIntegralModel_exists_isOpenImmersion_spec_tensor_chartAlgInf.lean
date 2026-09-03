import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgInf

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
universe u
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isOpenImmersion_spec_tensor_chartAlgInf
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (O : Type u) [CommRing O] [Algebra R O] :
    ∃ g : Spec (CommRingCat.of (↥(chartAlgInf R F j) ⊗[R] O)) ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))),
      IsOpenImmersion g ∧
      g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgInf R F j)) (B := O))) ≫
          ιInf R F j ∧
      g ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgInf R F j)) (B := O)).toRingHom) ∧
      Set.range g.base = ((pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤) :
        Set ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgInf.solution
