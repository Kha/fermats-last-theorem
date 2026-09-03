import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FnTwist
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_hasArchType0_archWeightCharFamily_two

set_option autoImplicit false

open NumberField AutomorphicForm

theorem CuspForm.IsAdelicLiftOfGamma1.hasArchType0_archWeightCharFamily_two
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    HasArchType₀ ℚ (archWeightCharFamily ℚ 2) Φ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_hasArchType0_archWeightCharFamily_two.solution
