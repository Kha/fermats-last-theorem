import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Sol.S_ModularCurve_coeffEmb_qExpand
import P2M.Util
namespace P2MW.S_ModularCurve_heckeBetaBar_coeffEmb

open ModularCurve AlgebraicCurve AlgebraicCurve.SemilinearAut IntermediateField HahnSeries

theorem solution {L : Type*} [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero ℓ] {x : LaurentSeries ℚ} (hx : x ∈ ModularCurve.modularFunctionFieldFull N) : ((ModularCurve.heckeBetaBar L N ℓ ⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (N * ℓ))) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ ℓ x) :=
  by
  rw [coe_heckeBetaBar, coeffEmb_qExpand]
