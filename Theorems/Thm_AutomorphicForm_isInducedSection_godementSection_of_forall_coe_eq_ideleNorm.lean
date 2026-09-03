import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_InducedSection
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isInducedSection_godementSection_of_forall_coe_eq_ideleNorm

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal AutomorphicForm

theorem AutomorphicForm.isInducedSection_godementSection_of_forall_coe_eq_ideleNorm
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [MeasurableMul (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsMulLeftInvariant]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (godementSection F ν₀ μ ν α hα Φ s) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isInducedSection_godementSection_of_forall_coe_eq_ideleNorm.solution
