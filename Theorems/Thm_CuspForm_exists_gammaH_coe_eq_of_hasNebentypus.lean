import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gammaH_coe_eq_of_hasNebentypus
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (hε : ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.HasNebentypus ε g) :
    ∃ f : CuspForm (CohCarrier.GammaH M H) k, (⇑f : UpperHalfPlane → ℂ) = ⇑g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus.solution
