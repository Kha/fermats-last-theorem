import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrableOn_and_setIntegral_mul_constantTerm_finsum_borelSigmaConjClassOrbit_eq_inv_measure_mul_tsum_integral_integral
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

theorem AutomorphicForm.integrableOn_and_setIntegral_mul_constantTerm_finsum_borelSigmaConjClassOrbit_eq_inv_measure_mul_tsum_integral_integral
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (t' : GL (Fin 2) L) (ht'u : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht'l : (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0 / (t' : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (J : Set (GL (Fin 2) L))
    (hJ : ∀ γ, γ ∈ J ↔ ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      t'⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L))
    (M : Subgroup (GL (Fin 2) L))
    (hM : ∀ m, m ∈ M ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t'⁻¹ * (m * t' * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {κ : Type} (a : κ → GL (Fin 2) L)
    (haD : ∀ j, ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((a j : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (ha : ∀ d : GL (Fin 2) L, (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (d : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∃! j, (a j)⁻¹ * d ∈ M)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    {j : κ | ∃ (w : (AdeleRing (𝓞 L) L)ˣ) (t : AdeleRing (𝓞 L) L),
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t *
            (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)))) ≠
          0}.Finite ∧
    (∀ (j : κ) (w : (AdeleRing (𝓞 L) L)ˣ), Integrable (fun t : AdeleRing (𝓞 L) L =>
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t *
            (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)))))
        (adelicAddHaar (𝓞 L) L)) ∧
    (∀ j : κ, Integrable (fun w : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) *
        ∫ t, φ (((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t *
            (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x))))
          ∂(adelicAddHaar (𝓞 L) L)) νZL) ∧
    (∀ z : (AdeleRing (𝓞 L) L)ˣ, Integrable (fun q : AdeleRing (𝓞 L) L =>
        ∑ᶠ γ ∈ J, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.unipotentGL2 q * (AutomorphicForm.centralScalar (𝓞 L) L z * x))))
        (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))) ∧
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ J, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL ∧
    (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ J, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL) =
      ((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal : ℂ)⁻¹ *
        ∑' j : κ, ∫ w, ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) *
          ∫ t, φ (((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t' *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t *
              (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L (a j))⁻¹ * x))))
            ∂(adelicAddHaar (𝓞 L) L) ∂νZL := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrableOn_and_setIntegral_mul_constantTerm_finsum_borelSigmaConjClassOrbit_eq_inv_measure_mul_tsum_integral_integral.solution
