import Definitions.Def_AutomorphicForm_GodementSection
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.TateGlobal AutomorphicForm

theorem NumberField.AdelicFourier.exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) :
    (∀ K : Set (AdelicGL2 (𝓞 F) F), IsCompact K → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ m ∈ K, ∀ t : (AdeleRing (𝓞 F) F)ˣ,
        Summable (fun ξ : Fin 2 → F =>
          ‖Φ ((t : AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
                (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) ∧
        ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            ‖Φ ((t : AdeleRing (𝓞 F) F) •
                Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                  (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖
          ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N)) ∧
    Continuous (fun m : AdelicGL2 (𝓞 F) F =>
      ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ (Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
          (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2.solution
