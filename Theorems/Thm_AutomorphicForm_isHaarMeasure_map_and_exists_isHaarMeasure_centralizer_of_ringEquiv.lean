import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf A) μ)
    (γ : GL (Fin 2) A)
    (τ' : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)))
      (centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ)))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ)) τ') :
    @Measure.IsHaarMeasure _ _ _ (glBorelOf B)
        (@Measure.map _ _ (glBorelOf A) (glBorelOf B) (Matrix.GeneralLinearGroup.map e.toRingHom) μ) ∧
      ∃ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ ∧
        (letI := glBorelOf B; letI := centralizerBorel A γ;
          letI := centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ);
          Measure.map (fun t : Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t : GL (Fin 2) B)) τ' =
            Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
              Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv.solution
