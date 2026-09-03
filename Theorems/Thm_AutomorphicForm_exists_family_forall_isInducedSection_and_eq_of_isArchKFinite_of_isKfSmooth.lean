import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_family_forall_isInducedSection_and_eq_of_isArchKFinite_of_isKfSmooth
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped NNReal

theorem AutomorphicForm.exists_family_forall_isInducedSection_and_eq_of_isArchKFinite_of_isKfSmooth
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (s₀ : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ α hα s₀) (AutomorphicForm.etaSnd ν α hα s₀) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ),
    ∃ Φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      Φ s₀ = φ ∧
      (∀ s, AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ α hα s) (AutomorphicForm.etaSnd ν α hα s) (Φ s)) ∧
      (∀ s, AutomorphicForm.IsArchKFinite F (Φ s)) ∧
      (∀ s, AutomorphicForm.IsKfSmooth F (Φ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => Φ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => Φ s g)) ∧
      (∀ w : NumberField.InfinitePlace F,
        ∃ W : Submodule ℂ (↥(AutomorphicForm.archRowIsometrySubgroup F w) → ℂ),
          FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
            (fun k : ↥(AutomorphicForm.archRowIsometrySubgroup F w) =>
              Φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_family_forall_isInducedSection_and_eq_of_isArchKFinite_of_isKfSmooth.solution
