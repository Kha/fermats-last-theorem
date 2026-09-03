import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_lintegral_comp_conj_twistedCentralizer_eq_mul_inv_one_sub_mul_inv_one_sub_of_map_eq_smul_map_toTensorGL_localHaar

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.lintegral_comp_conj_twistedCentralizer_eq_mul_inv_one_sub_mul_inv_one_sub_of_map_eq_smul_map_toTensorGL_localHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ))
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (tv : ℝ≥0∞)
    (hτ' : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ' =
          tv • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)))
    (s : ℝ) (Ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞)
    (hΨm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] Ψ)
    (hΨ1 : ∀ g : GL (Fin 2) (v.adicCompletion K),
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) →
        Ψ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) g) =
          ((‖((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖₊ : ℝ≥0∞) ^ s))
    (hΨ0 : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) →
        Ψ (AutomorphicForm.toTensorGL K L (v.adicCompletion K) g) = 0) :
    ∫⁻ t, Ψ (y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) ∂τ' =
      tv * ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-s))⁻¹ *
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - s))⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_lintegral_comp_conj_twistedCentralizer_eq_mul_inv_one_sub_mul_inv_one_sub_of_map_eq_smul_map_toTensorGL_localHaar.solution
