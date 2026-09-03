import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_isKfSmooth_weightOneLift
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open scoped ModularForm MatrixGroups

theorem LanglandsTunnell.isKfSmooth_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f) :
    IsKfSmooth ℚ (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_isKfSmooth_weightOneLift.solution
