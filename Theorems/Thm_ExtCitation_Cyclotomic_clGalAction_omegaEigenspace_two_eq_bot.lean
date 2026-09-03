import Definitions.Def_ClassGroup_GaloisAction
import Definitions.Def_Stickelberger_Basic
import P2M.Util
import P2M.Sol.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot
attribute [-instance] ExtCitation.Cyclotomic.instIsCycExt
attribute [-simp] ExtCitation.Cyclotomic.unitsEnd_proj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ExtCitation.Cyclotomic
open NumberField JacobiSumStickelberger Stickelberger
variable (p : ℕ) [Fact p.Prime]
theorem clGalAction_omegaEigenspace_two_eq_bot (hp5 : 5 ≤ p) :
    ∀ a : ClGalModule p (𝓞 (CyclotomicField p ℚ)),
      IsOmegaEigenvector (clGalAction p (CyclotomicField p ℚ)) 2 a →
        a = 0 := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot.solution
