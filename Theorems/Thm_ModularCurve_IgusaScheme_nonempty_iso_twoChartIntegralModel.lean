import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_nonempty_iso_twoChartIntegralModel

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.nonempty_iso_twoChartIntegralModel
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ e : ModularCurve.IgusaScheme N ℓ ≅
        AlgebraicCurve.TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) (jFull N),
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.toBase _ _ _ = igusaTo N ℓ ∧
      ιFin N ℓ ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιFin _ _ _ ∧
      ιInf N ℓ ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιInf _ _ _ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_nonempty_iso_twoChartIntegralModel.solution
