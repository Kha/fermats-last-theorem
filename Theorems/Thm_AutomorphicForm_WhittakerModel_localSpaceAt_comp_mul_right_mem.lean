import Definitions.Def_AutomorphicForm_WhittakerModelMultiplicityOne
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WhittakerModel_localSpaceAt_comp_mul_right_mem

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem AutomorphicForm.WhittakerModel.localSpaceAt_comp_mul_right_mem
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ p φ,
      ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ p φ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WhittakerModel_localSpaceAt_comp_mul_right_mem.solution
