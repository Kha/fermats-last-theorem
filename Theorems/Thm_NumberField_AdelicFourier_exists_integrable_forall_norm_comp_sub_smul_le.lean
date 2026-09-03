import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_integrable_forall_norm_comp_sub_smul_le

set_option autoImplicit false

open NumberField NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain NumberField.TateGlobal

theorem NumberField.AdelicFourier.exists_integrable_forall_norm_comp_sub_smul_le
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (e : mixedEmbedding.mixedSpace F) :
    ∃ bound : AdeleRing (𝓞 F) F → ℝ, Integrable bound μ ∧
      ∀ (x : AdeleRing (𝓞 F) F) (t : ℝ), t ∈ Metric.ball (0 : ℝ) 1 →
        ‖B (x - @id (AdeleRing (𝓞 F) F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e), 0))‖ ≤ bound x := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_integrable_forall_norm_comp_sub_smul_le.solution
