import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (w : NumberField.InfinitePlace K) (w' : NumberField.InfinitePlace L) (hw'w : w'.comap (algebraMap K L) = w)
    (hw : w.IsReal) (hw' : w'.IsComplex) :
    ∃ (e : NumberField.mixedEmbedding.mixedSpace L ≃L[ℝ] (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)))) (κ : NNReal), κ ≠ 0 ∧
      Measure.map (fun y : (L ⊗[K] InfiniteAdeleRing K) => e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))) lam =
        κ • ((volume : Measure ℂ).prod
          ((volume : Measure ({v : NumberField.InfinitePlace L // v.IsReal} → ℝ)).prod
            (volume : Measure ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)))) ∧
      (∀ y : (L ⊗[K] InfiniteAdeleRing K), (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))).1 = (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩) ∧
      ∀ (r : (L ⊗[K] InfiniteAdeleRing K)) (c : (InfiniteAdeleRing K)ˣ),
        (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r →
      ∀ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K),
        (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) →
        (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) →
      (∀ y : (L ⊗[K] InfiniteAdeleRing K),
        ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ =
          ‖(starRingEnd ℂ) ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩) +
            (starRingEnd ℂ) ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L r)).2 ⟨w', hw'⟩) * (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩‖) ∧
      ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ =
        |1 - ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L r)).2 ⟨w', hw'⟩‖ ^ 2| := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap.solution
