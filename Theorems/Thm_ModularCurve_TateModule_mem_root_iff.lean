import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_ModularCurve_TateModule_mem_root_iff

theorem ModularCurve.TateModule.mem_root_iff (p : ℕ) (J : Type) [AddCommGroup J]
    [Module ModularCurve.HeckeAlg J] (x : ℕ → J) :
    x ∈ _root_.TateModule p J ↔ x ∈ ModularCurve.TateModule p J := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TateModule_mem_root_iff.solution
