import Definitions.Def_AutomorphicForm_GodementSection
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.TateGlobal AutomorphicForm

theorem NumberField.AdelicFourier.exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat
    (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 ℚ)
    (K : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m ∈ K, ∀ (x : AdeleRing (𝓞 ℚ) ℚ) (a b : (AdeleRing (𝓞 ℚ) ℚ)ˣ),
        (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 → (b : AdeleRing (𝓞 ℚ) ℚ).2 = 1 →
        Summable (fun ξ : Fin 2 → ℚ =>
          ‖Φ (Matrix.vecMul
              ![(a : AdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ 0),
                (b : AdeleRing (𝓞 ℚ) ℚ) *
                  (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ 0) * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ 1))]
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖) ∧
        ∑' ξ : {ξ : Fin 2 → ℚ // ξ ≠ 0},
          ‖Φ (Matrix.vecMul
              ![(a : AdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ.1 0),
                (b : AdeleRing (𝓞 ℚ) ℚ) *
                  (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ.1 0) * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (ξ.1 1))]
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))‖
          ≤ C * (1 + (ideleNorm ℚ a)⁻¹) * (1 + (ideleNorm ℚ b)⁻¹)
              * (min 1 ((ideleNorm ℚ a)⁻¹ ^ N) + min 1 ((ideleNorm ℚ b)⁻¹ ^ N)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_mul_one_add_inv_ideleNorm_of_mem_schwartzBruhat2_rat.solution
