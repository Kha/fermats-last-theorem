import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv
attribute [-simp] RestrictedProduct.mapAlongLinearMap_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (ωR : ∀ w : InfinitePlace K, w.IsReal → (ℝˣ →* ℂˣ))
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal), Continuous fun t : ℝˣ => ((ωR w hw t : ℂˣ) : ℂ))
    (ωC : ∀ w : InfinitePlace K, w.IsComplex → (ℂˣ →* ℂˣ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), Continuous fun z : ℂˣ => ((ωC w hw z : ℂˣ) : ℂ))
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    ∃ C' : Set (AdelicGL2 (𝓞 K) K), IsCompact C' ∧ C ⊆ C' ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, b (g * u) = b g) →
        (∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ) (g : AdelicGL2 (𝓞 K) K),
            b (g * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t)) =
              ((ωR w hw t : ℂˣ) : ℂ) * b g) →
        (∀ (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ) (g : AdelicGL2 (𝓞 K) K),
            b (g * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z)) =
              ((ωC w hw z : ℂˣ) : ℂ) * b g) →
        (∀ l, l.length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b))) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ l, l.length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K →
            eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict C') ≤ ENNReal.ofReal M) →
          ∀ x ∈ C, ‖b x‖ ≤ c * M := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le.solution
