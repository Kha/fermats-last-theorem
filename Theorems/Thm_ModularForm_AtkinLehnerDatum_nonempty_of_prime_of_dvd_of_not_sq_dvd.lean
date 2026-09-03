import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd

theorem ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd {M q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) (hsq : ¬ q ^ 2 ∣ M) :
    Nonempty (ModularForm.AtkinLehnerDatum M q) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd.solution
