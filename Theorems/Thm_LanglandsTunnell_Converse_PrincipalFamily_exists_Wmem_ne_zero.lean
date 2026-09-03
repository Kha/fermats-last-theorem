import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero
attribute [-simp] AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply

set_option autoImplicit false

open LanglandsTunnell.Converse.PrincipalFamily

theorem LanglandsTunnell.Converse.PrincipalFamily.exists_Wmem_ne_zero (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    ∃ g : GL (Fin 2) ℝ, Wmem u₁ u₂ a₁ a₂ (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_PrincipalFamily_exists_Wmem_ne_zero.solution
