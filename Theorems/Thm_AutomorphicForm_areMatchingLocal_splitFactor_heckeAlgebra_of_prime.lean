import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import P2M.Util
import P2M.Sol.S_AutomorphicForm_areMatchingLocal_splitFactor_heckeAlgebra_of_prime

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.areMatchingLocal_splitFactor_heckeAlgebra_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      (Fin (Module.finrank K L) → v.adicCompletion K))
    (i₀ : Fin (Module.finrank K L))
    (U : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hU : U = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
    (f₁ : HeckePair.HeckeAlgebra U ℂ) :
    AreMatchingLocal K L v σ
      (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        (f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ)
            (Matrix.GeneralLinearGroup.map
              ((Pi.evalAlgHom (v.adicCompletion K) (fun _ => v.adicCompletion K) i₀).comp
                e.toAlgHom).toRingHom g) *
          ({h : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
              ∀ i : Fin (Module.finrank K L), i ≠ i₀ →
                Matrix.GeneralLinearGroup.map
                    ((Pi.evalAlgHom (v.adicCompletion K) (fun _ => v.adicCompletion K) i).comp
                      e.toAlgHom).toRingHom h ∈ U}.indicator (fun _ => (1 : ℂ)) g))
      (f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_areMatchingLocal_splitFactor_heckeAlgebra_of_prime.solution
