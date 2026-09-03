import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.SplitPlace.continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (ι : L →ₐ[K] A)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μL)
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (AutomorphicForm.glBorelOf A) μA) :
    letI : MeasurableSpace (GL (Fin 2) A) := AutomorphicForm.glBorelOf A
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.glBorelOf (L ⊗[K] A)
    Continuous (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ) ∧
    Continuous (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ).symm ∧
    (∀ (g : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.sigmaGL K L A σ g) j =
        AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ g (j + 1)) ∧
    (∀ g : GL (Fin 2) A,
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.toTensorGL K L A g) = fun _ => g) ∧
    (∀ (δ : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.normString K L A σ δ) j =
        (List.ofFn fun k : Fin (Module.finrank K L - 1 + 1) =>
          AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ δ (j + k)).prod) ∧
    (∀ δ : GL (Fin 2) (L ⊗[K] A),
      AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ (AutomorphicForm.normString K L A σ δ) 0 =
        (List.ofFn (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ δ)).prod) ∧
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ) μL =
        c • Measure.pi (fun _ : Fin (Module.finrank K L - 1 + 1) => μA) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi.solution
