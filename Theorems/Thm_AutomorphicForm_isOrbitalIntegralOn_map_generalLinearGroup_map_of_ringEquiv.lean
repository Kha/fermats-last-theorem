import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)))
      (centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ)))
    (hτ : letI := glBorelOf B; letI := centralizerBorel A γ;
      letI := centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ);
      Measure.map (fun t : Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t : GL (Fin 2) B)) τ' =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
          Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ)
    (f : GL (Fin 2) A → ℂ) (I : ℂ) (h : IsOrbitalIntegralOn A μ γ τ f I) :
    IsOrbitalIntegralOn B
      (@Measure.map _ _ (glBorelOf A) (glBorelOf B) (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
      (Matrix.GeneralLinearGroup.map e.toRingHom γ) τ'
      (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) I := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv.solution
