import Definitions.Def_LanglandsTunnell_ExplicitLift
import Mathlib.Algebra.Group.Submonoid.Membership
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero

theorem LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hg : g.det ≠ 0) :
    ∃ M ∈ Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))),
      M.map FLT.ExplicitLift.red = g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero.solution
