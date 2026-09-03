import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_hom_isFinite_surjective_of_algHom
    (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [CharZero F'] [Algebra R F] [Algebra R F']
    (φ : F →ₐ[R] F') (hφ : φ.toRingHom.Finite)
    (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (hj : φ j = j')
    (hFfin : IsNoetherianRing ↥(chartAlgFin R F j) ∧ IsFractionRing ↥(chartAlgFin R F j) F)
    (hFinf : IsNoetherianRing ↥(chartAlgInf R F j) ∧ IsFractionRing ↥(chartAlgInf R F j) F) :
    ∃ (m : AlgebraicCurve.TwoChartIntegralModel R F' j' ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
      (ιF : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j'))
      (ιI : ↥(chartAlgInf R F j) →ₐ[R] ↥(chartAlgInf R F' j')),
      (∀ x, (ιF x : F') = φ x) ∧ (∀ x, (ιI x : F') = φ x) ∧
      m ≫ toBase R F j = toBase R F' j' ∧
      Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F j = ιFin R F' j' ≫ m ∧
      Spec.map (CommRingCat.ofHom ιI.toRingHom) ≫ ιInf R F j = ιInf R F' j' ≫ m ∧
      m ⁻¹ᵁ (ιFin R F j).opensRange = (ιFin R F' j').opensRange ∧
      m ⁻¹ᵁ (ιInf R F j).opensRange = (ιInf R F' j').opensRange ∧
      IsFinite m ∧ Function.Surjective m.base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_of_algHom.solution
