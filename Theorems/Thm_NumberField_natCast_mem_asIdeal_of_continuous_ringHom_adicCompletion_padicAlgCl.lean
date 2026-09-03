import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_NumberField_natCast_mem_asIdeal_of_continuous_ringHom_adicCompletion_padicAlgCl
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem NumberField.natCast_mem_asIdeal_of_continuous_ringHom_adicCompletion_padicAlgCl
    (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K))
    (Φ : w.adicCompletion K →+* PadicAlgCl q) (hΦ : Continuous Φ) :
    ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_NumberField_natCast_mem_asIdeal_of_continuous_ringHom_adicCompletion_padicAlgCl.solution
