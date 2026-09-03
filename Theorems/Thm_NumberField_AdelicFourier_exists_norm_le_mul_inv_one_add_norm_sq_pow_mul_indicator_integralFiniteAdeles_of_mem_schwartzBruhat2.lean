import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicFourier NumberField.AdelicBox~exists_eq_sum_indicator_pi_image_integralFiniteAdeles IsDedekindDomain"
open scoped Classical

theorem NumberField.AdelicFourier.exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    (Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΨ : Ψ ∈ schwartzBruhat2 F) (M : ℕ) :
    ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ 0 < n ∧ ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
      ‖Ψ x‖ ≤ C * ((1 + ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1‖ ^ 2) ^ M)⁻¹ *
        Set.indicator {x : Fin 2 → AdeleRing (𝓞 F) F |
            ∀ i, ((n : ℕ) : FiniteAdeleRing (𝓞 F) F) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F}
          (fun _ => (1 : ℝ)) x := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2.solution
