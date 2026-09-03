import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AdelicDock_finEmbed_localEmbed_comm_of_ne

set_option autoImplicit false

open IsDedekindDomain

theorem AdelicDock.finEmbed_localEmbed_comm_of_ne {R : Type*} {K : Type*} [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {v w : HeightOneSpectrum R} (hvw : v ≠ w)
    (x : GL (Fin 2) (v.adicCompletion K)) (y : GL (Fin 2) (w.adicCompletion K)) :
    finEmbed R K (localEmbed R K v x) * finEmbed R K (localEmbed R K w y) =
      finEmbed R K (localEmbed R K w y) * finEmbed R K (localEmbed R K v x) := by p2m_exact_reverting @_root_.P2MW.S_AdelicDock_finEmbed_localEmbed_comm_of_ne.solution
