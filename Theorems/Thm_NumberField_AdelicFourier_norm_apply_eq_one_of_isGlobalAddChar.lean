import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar

open NumberField AutomorphicForm
theorem NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (x : AdeleRing (𝓞 F) F) :
    ‖ψ x‖ = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.solution
