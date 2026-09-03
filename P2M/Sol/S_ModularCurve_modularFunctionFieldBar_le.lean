import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_laurentBaseChange_mono
import P2M.Util
namespace P2MW.S_ModularCurve_modularFunctionFieldBar_le

open ModularCurve AlgebraicCurve IntermediateField HahnSeries

theorem solution (N : ℕ) [NeZero N] {M : ℕ} [NeZero M] (h : N ∣ M) : ModularCurve.modularFunctionFieldBar N ≤ ModularCurve.modularFunctionFieldBar M :=
  laurentBaseChange_mono _ (full_degeneracy_le h)
