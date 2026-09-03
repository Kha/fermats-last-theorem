import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_AutomorphicForm_continuous_whittakerCoefficient

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm

theorem AutomorphicForm.continuous_whittakerCoefficient
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (α : F) :
    Continuous (fun g : AdelicGL2 (𝓞 F) F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuous_whittakerCoefficient.solution
