import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped TensorProduct in

theorem AutomorphicForm.exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : GL (Fin 2) (InfiniteAdeleRing L))
    (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ g : GL (Fin 2) (AdeleRing (𝓞 L) L),
      AdelicLevel.glArch (𝓞 L) L g = a ∧
      (∀ v ∈ S, AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) = x v) ∧
      ∀ v ∉ S, AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) ∈
        AutomorphicForm.semiLocalIntegralSet K L v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_glArch_eq_and_semiLocalComponent_glFin_eq_and_mem_semiLocalIntegralSet.solution
