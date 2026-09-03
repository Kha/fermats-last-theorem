import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AdelicDock_isCompact_localLevelOne

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AdelicDock.isCompact_localLevelOne
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    (v : HeightOneSpectrum R) (N : Ideal R) :
    IsCompact (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by p2m_exact_reverting @_root_.P2MW.S_AdelicDock_isCompact_localLevelOne.solution
