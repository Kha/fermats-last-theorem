import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import P2M.Util
import P2M.Sol.S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul

theorem CuspForm.HasNebentypus.diamondLinOne_apply_eq_smul {M : ℕ} {k : ℤ}
    {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) k}
    (hg : CuspForm.HasNebentypus ε g) {d : ℕ} (hd : Nat.Coprime d M) :
    CuspForm.diamondLinOne M k d g = ε (d : ZMod M) • g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul.solution
