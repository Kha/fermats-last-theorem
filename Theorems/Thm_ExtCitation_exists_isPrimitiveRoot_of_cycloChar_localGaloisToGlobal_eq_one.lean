import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation
theorem ExtCitation.exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q))
    (hK : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, σ ∈ K.fixingSubgroup → cycloChar p (localGaloisToGlobal q σ) = 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ p := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one.solution
