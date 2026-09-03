import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_glArch_eq_and_finComponent_glFin_eq_and_mem_localIntegralSet
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.exists_glArch_eq_and_finComponent_glFin_eq_and_mem_localIntegralSet
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : GL (Fin 2) (InfiniteAdeleRing K))
    (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)) :
    ∃ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      AdelicLevel.glArch (𝓞 K) K g = a ∧
      (∀ v ∈ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) = x v) ∧
      ∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
        AutomorphicForm.localIntegralSet K v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_glArch_eq_and_finComponent_glFin_eq_and_mem_localIntegralSet.solution
