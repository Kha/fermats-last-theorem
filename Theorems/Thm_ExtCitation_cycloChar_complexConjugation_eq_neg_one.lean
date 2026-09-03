import Mathlib
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import P2M.Util
import P2M.Sol.S_ExtCitation_cycloChar_complexConjugation_eq_neg_one
open ExtCitation
theorem ExtCitation.cycloChar_complexConjugation_eq_neg_one
    (p : ℕ) [Fact p.Prime] :
    cycloChar p complexConjugation = -1 := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_cycloChar_complexConjugation_eq_neg_one.solution
