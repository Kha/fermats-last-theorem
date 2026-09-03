import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_monoidHom_localCentralizer_isCompact_ker_of_isRegularSemisimple

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.exists_monoidHom_localCentralizer_isCompact_ker_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    ∃ χ : AutomorphicForm.localCentralizer K v γ →* Multiplicative (Fin 2 → ℤ),
      IsCompact (Subtype.val '' (χ.ker : Set (AutomorphicForm.localCentralizer K v γ))) ∧
        IsOpen (χ.ker : Set (AutomorphicForm.localCentralizer K v γ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_monoidHom_localCentralizer_isCompact_ker_of_isRegularSemisimple.solution
