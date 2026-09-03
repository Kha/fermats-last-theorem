import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal

set_option autoImplicit false
open ExtCitation
theorem ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
    (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime] :
    ∃ ζ : (PadicAlgCl q)ˣ, IsPrimitiveRoot ζ p ∧ ∀ g : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      g • ζ = ζ ^ (cycloChar p (localGaloisToGlobal q g) : ZMod p).val := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal.solution
