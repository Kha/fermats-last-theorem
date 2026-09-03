import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime

set_option autoImplicit false
theorem ModularForm.AtkinLehnerDatum.not_dvd_R_of_prime {M q : ℕ}
    (W : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) : ¬ q ∣ W.R := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime.solution
