import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_eq_algebraMap_of_mem_chartAlgFin_of_mem_chartAlgInf

open ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_eq_algebraMap_of_mem_chartAlgFin_of_mem_chartAlgInf
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (x : ↥(modularFunctionFieldFull N)) (hx0 : x ∈ chartAlgFin N ℓ) (hx1 : x ∈ chartAlgInf N ℓ) :
    ∃ r : ↥(GaloisRep.ratLocalizedAt ℓ),
      x = algebraMap ℚ ↥(modularFunctionFieldFull N) (r : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_eq_algebraMap_of_mem_chartAlgFin_of_mem_chartAlgInf.solution
