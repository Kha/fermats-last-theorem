import Definitions.Def_LanglandsTunnell_ExplicitLift
import Mathlib.Algebra.Group.Submonoid.Membership
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ExplicitLift_map_red_injOn_closure

theorem LanglandsTunnell.ExplicitLift.map_red_injOn_closure :
    Set.InjOn (fun M : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) => M.map FLT.ExplicitLift.red)
      (Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ExplicitLift_map_red_injOn_closure.solution
