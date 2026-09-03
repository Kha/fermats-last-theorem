import Definitions.Def_AutomorphicForm_GodementSection
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact

set_option autoImplicit false

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.AdelicFourier.exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F)
    (K : Set (AdelicGL2 (𝓞 F) F)) (hK : IsCompact K) :
    ∃ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ, Ψ ∈ schwartzBruhat2 F ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, (((Ψ x).re : ℝ) : ℂ) = Ψ x ∧ 0 ≤ (Ψ x).re) ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, ‖Φ x‖ ≤ (Ψ x).re) ∧
      ∀ g ∈ K, ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
        ‖Φ (Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖ ≤ (Ψ x).re := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact.solution
