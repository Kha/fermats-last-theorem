import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_CuspForm_atkinLehnerLin_atkinLehnerLin_eq_smul
import P2M.Util
namespace P2MW.S_CuspForm_atkinLehnerLin_atkinLehnerLin

open ModularForm

namespace CuspForm
p2m_export "CuspForm" "atkinLehnerLin atkinLehnerLin_atkinLehnerLin_eq_smul"
p2m_open "CuspForm"
variable {M q : ℕ}
end CuspForm

theorem solution {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    CuspForm.atkinLehnerLin W 2 (CuspForm.atkinLehnerLin W 2 f) = f := by
  rw [CuspForm.atkinLehnerLin_atkinLehnerLin_eq_smul]
  norm_num
