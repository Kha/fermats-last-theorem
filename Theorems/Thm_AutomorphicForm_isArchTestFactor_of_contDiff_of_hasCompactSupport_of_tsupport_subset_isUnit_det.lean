import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem AutomorphicForm.isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det
    (F : Type) [Field F] [NumberField F] (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    IsArchTestFactor F fun g => Φ (archEntries F g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det.solution
