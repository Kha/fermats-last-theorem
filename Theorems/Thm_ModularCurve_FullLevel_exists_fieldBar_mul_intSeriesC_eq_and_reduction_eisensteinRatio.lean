import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups ArithmeticFunction.sigma

theorem ModularCurve.FullLevel.exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] :
    ∃ (u : fieldBar q M') (X Y : PowerSeries ℤ),
      (u : LaurentSeries (AlgebraicClosure ℚ)) * intSeriesC (AlgebraicClosure ℚ) Y =
        intSeriesC (AlgebraicClosure ℚ) X ∧
      ∀ (κ : Type) [Field κ] [CharP κ q],
        intSeriesC κ Y ≠ 0 ∧
        intSeriesC κ X * intSeriesC κ (PowerSeries.X * dedekindEtaUnit) =
          intSeriesC κ Y *
            (intSeriesC κ (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
              intSeriesC κ (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_fieldBar_mul_intSeriesC_eq_and_reduction_eisensteinRatio.solution
