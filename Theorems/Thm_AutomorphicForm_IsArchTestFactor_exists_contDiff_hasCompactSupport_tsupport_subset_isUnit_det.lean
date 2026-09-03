import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsArchTestFactor_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem AutomorphicForm.IsArchTestFactor.exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det
    (F : Type) [Field F] [NumberField F] {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchTestFactor F fa) :
    ∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
        tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} ∧ ∀ g, fa g = Φ (archEntries F g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsArchTestFactor_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det.solution
