import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

theorem NumberField.AdelicFourier.exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (M : ℕ) :
    ∃ I : ℝ, ∀ g ∈ C,
      Integrable (fun x : AdeleRing (𝓞 F) F => ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ ∧
      ∫ x, ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M ∂μ ≤ I := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat.solution
