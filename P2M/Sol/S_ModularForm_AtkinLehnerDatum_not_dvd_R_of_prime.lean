import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
namespace P2MW.S_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime

set_option autoImplicit false

theorem solution {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) :
    ¬ q ∣ W.R := by
  intro ⟨c, hc⟩
  have h1 : (q : ℤ) ∣ 1 := ⟨W.a - (c : ℤ) * W.b, by
    have hb := W.bezout; rw [hc] at hb; push_cast at hb; linarith⟩
  have hq1 : q = 1 := by
    have := Int.isUnit_iff.mp (isUnit_of_dvd_one h1)
    omega
  exact absurd hq1 hq.one_lt.ne'
