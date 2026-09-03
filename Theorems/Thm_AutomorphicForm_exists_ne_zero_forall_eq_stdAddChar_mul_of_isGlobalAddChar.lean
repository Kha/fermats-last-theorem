import Definitions.Def_NumberField_AdelicTraceFin
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar

open NumberField

theorem AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ a : F, a ≠ 0 ∧
      (∀ x : AdeleRing (𝓞 F) F,
        ψ x = StandardAddChar.stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) a * x)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar.solution
