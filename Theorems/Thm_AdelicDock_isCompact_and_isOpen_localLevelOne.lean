import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AdelicDock_isCompact_and_isOpen_localLevelOne

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AdelicDock.isCompact_and_isOpen_localLevelOne (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    IsCompact (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      IsOpen (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by p2m_exact_reverting @_root_.P2MW.S_AdelicDock_isCompact_and_isOpen_localLevelOne.solution
