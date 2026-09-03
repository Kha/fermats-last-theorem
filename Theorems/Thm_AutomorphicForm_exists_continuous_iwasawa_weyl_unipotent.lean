import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

theorem AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)),
    ∃ κ : AdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F,
      Continuous κ ∧
      (∀ x, glFin (𝓞 F) F (κ x) ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (κ x)))) ∧
      (∀ x, (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (κ x)⁻¹ ∈ adelicBorel (𝓞 F) F) ∧
      (∀ x y : AdeleRing (𝓞 F) F, ∀ v : HeightOneSpectrum (𝓞 F), x.2 v = y.2 v →
        finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ x)) = finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ y))) ∧
      (∀ x y : AdeleRing (𝓞 F) F, x.1 = y.1 → glArch (𝓞 F) F (κ x) = glArch (𝓞 F) F (κ y)) ∧
      (∀ (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ),
        IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ →
        ∀ x : AdeleRing (𝓞 F) F,
          φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) =
            ((adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) : ℝ) : ℂ) ^ (s + 1 / 2) * φ (κ x)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent.solution
