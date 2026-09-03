import Definitions.Def_ExtCitation_CyclotomicUnits
import P2M.Util
import P2M.Sol.S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ExtCitation.Cyclotomic
open NumberField JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]
theorem finrank_unitsOmegaEigenspace_two (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (unitsOmegaEigenspace p 2) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.solution
