import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain NumberField.TateGlobal

theorem AutomorphicForm.exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (hinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), G (globalPoints (𝓞 F) F γ * g) = G g)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (a : F) (ha : a ≠ 0)
    (hψa : ∀ x : InfiniteAdeleRing F,
      ψ (algebraMap F (InfiniteAdeleRing F) a * x, 0) =
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (e : mixedEmbedding.mixedSpace F) :
    ∃ B' : AdeleRing (𝓞 F) F → ℂ, B' ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      ∀ (Φ' : AdelicGL2 (𝓞 F) F → ℂ),
        (∀ h : AdelicGL2 (𝓞 F) F, Φ' h = (letI := adeleBorel (𝓞 F) F
          ∫ x, B' x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) →
        ∀ b : (AdeleRing (𝓞 F) F)ˣ,
          whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ Φ' 1 (diagOne b) =
            ((2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
                (InfiniteAdeleRing.ringEquiv_mixedSpace F
                    (algebraMap F (InfiniteAdeleRing F) a⁻¹ * (b : AdeleRing (𝓞 F) F).1) * e) : ℝ) : ℂ) *
              Complex.I *
            whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ Φ 1 (diagOne b) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul.solution
