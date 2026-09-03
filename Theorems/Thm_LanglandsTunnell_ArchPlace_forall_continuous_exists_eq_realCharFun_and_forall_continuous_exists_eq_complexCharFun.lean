import Definitions.Def_LanglandsTunnell_ArchPlace
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchPlace_forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun

set_option autoImplicit false

theorem
LanglandsTunnell.ArchPlace.forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun :
    (∀ χ : ℝˣ →* ℂˣ, Continuous χ → ∃ (u : ℂ) (a : ZMod 2), χ = realCharFun u a) ∧
      (∀ χ : ℂˣ →* ℂˣ, Continuous χ → ∃ (u : ℂ) (k : ℤ), χ = complexCharFun u k) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchPlace_forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun.solution
