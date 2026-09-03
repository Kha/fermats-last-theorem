import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq
    (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (e : F ≃ₐ[R] F') (he : e j = j') :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F' j')
      (eFin : chartAlgFin R F j →ₐ[R] chartAlgFin R F' j') (eInf : chartAlgInf R F j →ₐ[R] chartAlgInf R F' j'),
      (∀ x, (eFin x : F') = e x) ∧ (∀ x, (eInf x : F') = e x) ∧
      w.hom ≫ toBase R F' j' = toBase R F j ∧
      Spec.map (CommRingCat.ofHom eFin.toRingHom) ≫ ιFin R F j = ιFin R F' j' ≫ w.inv ∧
      Spec.map (CommRingCat.ofHom eInf.toRingHom) ≫ ιInf R F j = ιInf R F' j' ≫ w.inv := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq.solution
