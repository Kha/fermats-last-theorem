import Mathlib
import Definitions.Def_LanglandsTunnell_ExplicitLift
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ExplicitLift_exists_monoidHom_map_red_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem LanglandsTunnell.ExplicitLift.exists_monoidHom_map_red_eq :
    ∃ Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)),
      (∀ g : GL (Fin 2) (ZMod 3), Matrix.GeneralLinearGroup.map FLT.ExplicitLift.red (Ψ g) = g) ∧
      (∀ g : GL (Fin 2) (ZMod 3), ((Ψ g : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) ∈
        Submonoid.closure
          ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2))))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ExplicitLift_exists_monoidHom_map_red_eq.solution
