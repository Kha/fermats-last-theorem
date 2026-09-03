import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin

open ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.isIntegrallyClosed_chartAlgFin (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsIntegrallyClosed ↥(chartAlgFin N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin.solution
