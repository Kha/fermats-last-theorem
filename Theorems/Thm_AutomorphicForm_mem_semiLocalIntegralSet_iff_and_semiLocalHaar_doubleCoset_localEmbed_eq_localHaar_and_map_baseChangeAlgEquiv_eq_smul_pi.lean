import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Pointwise ENNReal

theorem AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))] :
    (∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      g ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
        ∀ w : v.Extension (𝓞 L),
          Matrix.GeneralLinearGroup.map
              ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
                (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
                  L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)) g ∈
            AutomorphicForm.localIntegralSet L w.1) ∧
    (∀ (w₀ : v.Extension (𝓞 L)) (ρ : GL (Fin 2) (w₀.1.adicCompletion L)),
      Matrix.GeneralLinearGroup.map
          ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w₀).comp
            (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
              L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L))
          (AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 ρ)) = ρ ∧
      ∀ w : v.Extension (𝓞 L), w ≠ w₀ →
        Matrix.GeneralLinearGroup.map
            ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
              (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
                L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L))
            (AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 ρ)) = 1) ∧
    (∀ (w₀ : v.Extension (𝓞 L)) (ρ : GL (Fin 2) (w₀.1.adicCompletion L))
        (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      g ∈ AutomorphicForm.semiLocalIntegralSet K L v *
            {AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 ρ)} *
          AutomorphicForm.semiLocalIntegralSet K L v ↔
        Matrix.GeneralLinearGroup.map
              ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w₀).comp
                (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
                  L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)) g ∈
            AutomorphicForm.localIntegralSet L w₀.1 * ({ρ} : Set (GL (Fin 2) (w₀.1.adicCompletion L))) *
              AutomorphicForm.localIntegralSet L w₀.1 ∧
          ∀ w : v.Extension (𝓞 L), w ≠ w₀ →
            Matrix.GeneralLinearGroup.map
                ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
                  (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
                    L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)) g ∈
              AutomorphicForm.localIntegralSet L w.1) ∧
    (∀ (w₀ : v.Extension (𝓞 L)) (ρ : GL (Fin 2) (w₀.1.adicCompletion L)),
      AutomorphicForm.semiLocalHaar K L v
          (AutomorphicForm.semiLocalIntegralSet K L v *
              {AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 ρ)} *
            AutomorphicForm.semiLocalIntegralSet K L v) =
        AutomorphicForm.localHaar L w₀.1
          (AutomorphicForm.localIntegralSet L w₀.1 * ({ρ} : Set (GL (Fin 2) (w₀.1.adicCompletion L))) *
            AutomorphicForm.localIntegralSet L w₀.1)) ∧
    (∀ [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
        [∀ w : v.Extension (𝓞 L), MeasurableSpace (w.1.adicCompletion L)]
        [∀ w : v.Extension (𝓞 L), BorelSpace (w.1.adicCompletion L)]
        (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
        (νw : ∀ w : v.Extension (𝓞 L), Measure (w.1.adicCompletion L)) [∀ w, (νw w).IsAddHaarMeasure],
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        Measure.map (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v) ν = c • Measure.pi νw) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi.solution
