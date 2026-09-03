import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC

set_option autoImplicit false

open CongruenceSubgroup ModularCurve AlgebraicCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC
    (κ : Type) [Field κ] (M : ℕ) [NeZero M]
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (k : ℕ) (g : ModularForm (Gamma1 M) (k : ℤ)) (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC κ pg ≠ 0)
    (t : ↥(ModularCurve.x1FunctionFieldC κ M))
    (ht : (t : LaurentSeries κ) =
      intSeriesC κ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k) / intSeriesC κ (pg ^ 12))
    (x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)) (htx : x.ord t = 0) :
    (3 : ℤ) ∣ (k : ℤ) * x.ord J ∧
      (2 : ℤ) ∣ (k : ℤ) * x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC.solution
