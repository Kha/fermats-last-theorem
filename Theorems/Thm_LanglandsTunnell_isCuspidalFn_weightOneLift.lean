import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_isCuspidalFn_weightOneLift
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val

set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open scoped ModularForm MatrixGroups Manifold

theorem LanglandsTunnell.isCuspidalFn_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hzero : ∀ δ : SL(2, ℤ), IsZeroAtImInfty (f ∣[(1 : ℤ)] (δ : GL (Fin 2) ℝ))) :
    @IsCuspidalFn _ (productionPinsCompact ℚ).nS _ _ (productionPinsCompact ℚ).ν unipotentGL2
      (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_isCuspidalFn_weightOneLift.solution
