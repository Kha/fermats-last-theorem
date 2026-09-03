import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeBetaBar_coeffEmb

theorem ModularCurve.heckeBetaBar_coeffEmb {L : Type*} [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero ℓ] {x : LaurentSeries ℚ} (hx : x ∈ ModularCurve.modularFunctionFieldFull N) : ((ModularCurve.heckeBetaBar L N ℓ ⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (N * ℓ))) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ ℓ x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeBetaBar_coeffEmb.solution
