import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one

open NumberField AutomorphicForm
theorem NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (y : AdeleRing (𝓞 F) F)
    (hy : ∀ ξ : F, ψ (y * algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1) :
    y ∈ Set.range (algebraMap F (AdeleRing (𝓞 F) F)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one.solution
