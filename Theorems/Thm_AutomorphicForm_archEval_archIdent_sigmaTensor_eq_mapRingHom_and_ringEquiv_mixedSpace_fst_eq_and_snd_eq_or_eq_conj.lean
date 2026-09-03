import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (g : L ≃ₐ[K] L) (w' : NumberField.InfinitePlace L) :
    Isometry (((WithAbs.equiv w'.1).symm.toRingHom.comp
          ((g : L ≃ₐ[K] L).toRingEquiv.toRingHom.comp (WithAbs.equiv (w'.comap (g : L →+* L)).1).toRingHom)) :
        WithAbs (w'.comap (g : L →+* L)).1 → WithAbs w'.1) ∧
    (∀ h : Isometry (((WithAbs.equiv w'.1).symm.toRingHom.comp
          ((g : L ≃ₐ[K] L).toRingEquiv.toRingHom.comp (WithAbs.equiv (w'.comap (g : L →+* L)).1).toRingHom)) :
        WithAbs (w'.comap (g : L →+* L)).1 → WithAbs w'.1),
      ∀ y : (L ⊗[K] InfiniteAdeleRing K),
        (NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))).toCompletion =
          h.mapRingHom (NumberField.AdelicLevel.archEval L (w'.comap (g : L →+* L)) (AutomorphicForm.archIdent K L y)).toCompletion) ∧
    (∀ y : (L ⊗[K] InfiniteAdeleRing K),
      ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))‖ =
        ‖NumberField.AdelicLevel.archEval L (w'.comap (g : L →+* L)) (AutomorphicForm.archIdent K L y)‖) ∧
    (∀ (w'' : NumberField.InfinitePlace L) (hw' : w'.IsReal) (hw'' : w''.IsReal),
      w'' = w'.comap (g : L →+* L) →
      ∀ y : (L ⊗[K] InfiniteAdeleRing K),
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))).1 ⟨w', hw'⟩ =
          (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).1 ⟨w'', hw''⟩) ∧
    (∀ (w'' : NumberField.InfinitePlace L) (hw' : w'.IsComplex) (hw'' : w''.IsComplex),
      w'' = w'.comap (g : L →+* L) →
      (∀ y : (L ⊗[K] InfiniteAdeleRing K),
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))).2 ⟨w', hw'⟩ =
          (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w'', hw''⟩) ∨
      (∀ y : (L ⊗[K] InfiniteAdeleRing K),
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y))).2 ⟨w', hw'⟩ =
          (starRingEnd ℂ) ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w'', hw''⟩))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj.solution
