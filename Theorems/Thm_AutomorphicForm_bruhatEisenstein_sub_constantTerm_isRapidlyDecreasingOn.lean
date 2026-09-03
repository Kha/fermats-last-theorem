import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn
attribute [-instance] instCountableOfNumberField_definitions NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center
attribute [-simp] AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

open MeasureTheory NumberField NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel
open scoped NNReal

theorem AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn
    (F : Type) [Field F] [NumberField F] (c u : ℝ) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ) (_hφf : IsKfSmooth F φ) (_hφc : Continuous φ),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    ∃ T₀ : ℝ, IsRapidlyDecreasingOn
      (integralWindowedSiegelSet F c u ∩ {x | T₀ < archHeight F (glArch (𝓞 F) F x)})
      (fun g => archHeight F (glArch (𝓞 F) F g))
      (fun x => E x - @AutomorphicForm.constantTerm _ (NumberField.AdelicHaar.adeleBorel (𝓞 F) F) _ _
          (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 F) F)
            (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) E x) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn.solution
