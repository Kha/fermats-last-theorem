import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FnTwist
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOf_hasArchType0_archWeightCharFamily_two

set_option autoImplicit false

open NumberField AutomorphicForm

theorem CuspForm.IsAdelicLiftOf.hasArchType0_archWeightCharFamily_two
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hΦ : CuspForm.IsAdelicLiftOf g Φ) :
    HasArchType₀ ℚ (archWeightCharFamily ℚ 2) Φ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_hasArchType0_archWeightCharFamily_two.solution
