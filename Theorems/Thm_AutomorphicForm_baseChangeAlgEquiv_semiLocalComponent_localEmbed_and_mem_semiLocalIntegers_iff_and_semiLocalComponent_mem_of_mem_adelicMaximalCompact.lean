import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (∀ (w₀ : v.Extension (𝓞 L)) (g : GL (Fin 2) (w₀.1.adicCompletion L)) (i j : Fin 2),
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
          (((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 g) :
            GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) w₀ =
        (g : Matrix (Fin 2) (Fin 2) (w₀.1.adicCompletion L)) i j ∧
      ∀ w : v.Extension (𝓞 L), w ≠ w₀ →
        HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
            (((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w₀.1 g) :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) w =
          (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j) ∧
    (∀ y : L ⊗[K] v.adicCompletion K,
      y ∈ AutomorphicForm.semiLocalIntegers K L v ↔
        ∀ w : v.Extension (𝓞 L),
          HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w ∈ w.1.adicCompletionIntegers L) ∧
    (∀ k : AutomorphicForm.AdelicGL2 (𝓞 L) L, k ∈ AutomorphicForm.adelicMaximalCompact L →
      AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L k) ∈
        AutomorphicForm.semiLocalIntegralSet K L v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact.solution
