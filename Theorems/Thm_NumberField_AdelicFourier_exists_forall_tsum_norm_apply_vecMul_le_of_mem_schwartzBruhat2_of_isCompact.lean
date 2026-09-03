import Definitions.Def_AutomorphicForm_GodementSection
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_of_mem_schwartzBruhat2_of_isCompact
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.TateGlobal AutomorphicForm

theorem NumberField.AdelicFourier.exists_forall_tsum_norm_apply_vecMul_le_of_mem_schwartzBruhat2_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F)
    (K : Set (AdelicGL2 (𝓞 F) F)) (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m ∈ K, ∀ (x : AdeleRing (𝓞 F) F) (a b : (AdeleRing (𝓞 F) F)ˣ),
        (a : AdeleRing (𝓞 F) F).2 = 1 → (b : AdeleRing (𝓞 F) F).2 = 1 →
        Summable (fun ξ : Fin 2 → F =>
          ‖Φ (Matrix.vecMul
              ![(a : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) (ξ 0),
                (b : AdeleRing (𝓞 F) F) *
                  (algebraMap F (AdeleRing (𝓞 F) F) (ξ 0) * x + algebraMap F (AdeleRing (𝓞 F) F) (ξ 1))]
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖) ∧
        ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
          ‖Φ (Matrix.vecMul
              ![(a : AdeleRing (𝓞 F) F) * algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 0),
                (b : AdeleRing (𝓞 F) F) *
                  (algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 0) * x + algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 1))]
              (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))‖
          ≤ C * (1 + (ideleNorm F a)⁻¹ ^ 2) * (1 + (ideleNorm F b)⁻¹ ^ 2)
              * (min 1 ((ideleNorm F a)⁻¹ ^ N) + min 1 ((ideleNorm F b)⁻¹ ^ N)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_vecMul_le_of_mem_schwartzBruhat2_of_isCompact.solution
