import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SplitPlace_exists_ringEquiv_coords_semiLocalComponent_localEmbed_eq_mulSingle

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.SplitPlace.exists_ringEquiv_coords_semiLocalComponent_localEmbed_eq_mulSingle
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (w : v.Extension (𝓞 L)) (hsplit : v.asIdeal.inertiaDeg' w.1.asIdeal = 1)
    (ι : L →ₐ[K] v.adicCompletion K) :
    ∃ i₀ : Fin (Module.finrank K L - 1 + 1),
    ∃ e : w.1.adicCompletion L ≃+* v.adicCompletion K,
      (∀ x : w.1.adicCompletion L, Valued.v (e x) = Valued.v x) ∧
      ∀ g : GL (Fin 2) (w.1.adicCompletion L),
        AutomorphicForm.SplitPlace.coords (v.adicCompletion K) σ ι hprime hσ
            (AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1 g)) =
          Pi.mulSingle i₀ (Matrix.GeneralLinearGroup.map e.toRingHom g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SplitPlace_exists_ringEquiv_coords_semiLocalComponent_localEmbed_eq_mulSingle.solution
