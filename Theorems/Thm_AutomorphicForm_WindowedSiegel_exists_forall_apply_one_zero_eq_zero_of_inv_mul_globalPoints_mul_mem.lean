import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

open scoped NumberField

theorem AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
    (F : Type) [Field F] [NumberField F]
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} (hC : IsCompact C) :
    ∃ T₀ : ℝ, ∀ (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F),
      NumberField.AdelicLevel.glFin (𝓞 F) F x ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      NumberField.AdelicLevel.glFin (𝓞 F) F y ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F x) →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F y) →
      ∀ γ : GL (Fin 2) F,
        x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * y ∈ C →
          (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem.solution
