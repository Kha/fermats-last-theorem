import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_diamondLinOne_two_mem_range_ratCast_of_qCoeff_mem_range_intCast

set_option autoImplicit false

theorem CuspForm.qCoeff_diamondLinOne_two_mem_range_ratCast_of_qCoeff_mem_range_intCast
    (M : ℕ) [NeZero M]
    (hdia : ∀ d : ℕ, Nat.Coprime d M →
      ∃ σ : ModularCurve.x1FunctionField M ≃ₐ[ℚ] ModularCurve.x1FunctionField M,
        ModularCurve.IsDiamondAut M d σ)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ Set.range ((↑) : ℤ → ℂ))
    (d n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.diamondLinOne M 2 d f) n ∈ Set.range ((↑) : ℚ → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_diamondLinOne_two_mem_range_ratCast_of_qCoeff_mem_range_intCast.solution
