import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix

open UpperHalfPlane CongruenceSubgroup
open scoped ModularForm MatrixGroups
namespace ModularForm.AtkinLehnerDatum

variable {M q : ℕ} [NeZero M] (W : AtkinLehnerDatum M q)

lemma not_dvd_R (hq : 1 < q) : ¬ q ∣ W.R := by
  intro ⟨t, ht⟩
  have h : (q : ℤ) ∣ 1 := ⟨W.a - (t : ℤ) * W.b, by
    rw [← W.bezout, ht]; push_cast; ring⟩
  exact absurd (Int.eq_one_of_dvd_one (by exact_mod_cast q.zero_le) h)
    (by exact_mod_cast hq.ne')

end ModularForm.AtkinLehnerDatum
theorem CuspForm.traceLin_of_coe_eq_slash_heckeDiagMatrix {M q : ℕ}
    (W : ModularForm.AtkinLehnerDatum M q) [NeZero M] (hq : q.Prime)
    {f : CuspForm (Gamma0 W.R) 2} {g : CuspForm (Gamma0 M) 2}
    (hg : ⇑g = (⇑f) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) :
    traceLin W hq g = heckeTLin (2 : ℤ) hq (W.not_dvd_R hq.one_lt) f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.solution
