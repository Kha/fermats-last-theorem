import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import P2M.Util
import P2M.Sol.S_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (m : ℕ) (φ : Fin m → (AdelicGL2 (𝓞 F) F → ℂ)) (hφ : ∀ j, Continuous (φ j)) (cs : Fin m → ℂ)
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (fun x => ∑ j, cs j * φ j x) α g =
      ∑ j, cs j * whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (φ j) α g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous.solution
