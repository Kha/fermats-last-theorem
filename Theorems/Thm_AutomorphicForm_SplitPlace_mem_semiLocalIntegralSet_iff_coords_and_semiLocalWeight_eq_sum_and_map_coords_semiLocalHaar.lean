import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SplitPlace_mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.SplitPlace.mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ι : L →ₐ[K] v.adicCompletion K) :
    letI : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    (∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        x ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
          ∀ j, AutomorphicForm.SplitPlace.coords (v.adicCompletion K) σ ι hprime hσ x j ∈ AutomorphicForm.localIntegralSet K v) ∧
    (∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.semiLocalWeight K L v x =
          ∑ j, AutomorphicForm.LocalWeight.weight (AutomorphicForm.SplitPlace.coords (v.adicCompletion K) σ ι hprime hσ x j)) ∧
    Measure.map (AutomorphicForm.SplitPlace.coords (v.adicCompletion K) σ ι hprime hσ) (AutomorphicForm.semiLocalHaar K L v) =
      Measure.pi (fun _ => AutomorphicForm.localHaar K v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SplitPlace_mem_semiLocalIntegralSet_iff_coords_and_semiLocalWeight_eq_sum_and_map_coords_semiLocalHaar.solution
