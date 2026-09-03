import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple
attribute [-simp] AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
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
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (ω : L ⊗[K] InfiniteAdeleRing K → ℝ) (hω : Continuous ω)
    (a t : (InfiniteAdeleRing K)ˣ) (hreg : AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)))
    (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (hδ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t))) :
    letI : MeasurableSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := borel _
    Integrable
      (fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
            (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
            (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
          ((L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) =>
        φa (AutomorphicForm.archIdentGL K L
          ((p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
            (diagUnits2 (α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) (β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) *
              AutomorphicForm.unipotentGL2
                (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ p.2.1 -
                  (((α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
                    (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * p.2.1)) *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) *
          ((ω p.2.1 : ℝ) : ℂ))
      ((θ.prod θ).prod (lam.prod κ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple.solution
