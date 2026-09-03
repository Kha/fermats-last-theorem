import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled
attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions
attribute [-simp] AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
        (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker)
    [θ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ), AutomorphicForm.IsArchTestFactor L φa →
      ∀ (ω : L ⊗[K] InfiniteAdeleRing K → ℝ), Continuous ω →
      ∀ (W : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ), Continuous W →
        (∀ (u' t' : (L ⊗[K] InfiniteAdeleRing K)ˣ) (y : L ⊗[K] InfiniteAdeleRing K)
            (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
            k ∈ (⨅ w : InfinitePlace L,
              (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
                ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
                Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) →
            W (Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 t' 1 * AutomorphicForm.unipotentGL2 y * k) =
              ω y) →
      ∀ (a t : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        (∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
            ∫ x, g (x : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
              ∫ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 r.1 r.2) ∂(ρ.prod ρ)) →
      ∀ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ,
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
      ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (diagUnits2 α β))),
        τ'.IsHaarMeasure →
        AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) (diagUnits2 α β) 1 τ τ' →
      (∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L)
          (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) I' →
        I' = (c : ℂ) *
          ∫ u, ∫ y, @integral _ ℂ _ _ (borel _) κ (fun k =>
              φa (AutomorphicForm.archIdentGL K L
                ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
                  (diagUnits2 (α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) *
                    AutomorphicForm.unipotentGL2
                      (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y -
                        (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
                          (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * y)) *
                  AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) ∂lam
            ∂(θ.prod θ)) ∧
      (∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.archHaarL K L) W (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) J' →
        J' = (c : ℂ) *
          ∫ u, ∫ y, (@integral _ ℂ _ _ (borel _) κ (fun k =>
              φa (AutomorphicForm.archIdentGL K L
                ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
                  (diagUnits2 (α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) *
                    AutomorphicForm.unipotentGL2
                      (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y -
                        (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
                          (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * y)) *
                  AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))))) *
              ((ω y : ℝ) : ℂ) ∂lam
            ∂(θ.prod θ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled.solution
