import Mathlib
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import P2M.Util
import P2M.Sol.S_CuspForm_heckeTLinOne_slashOfMemGamma0

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.heckeTLinOne_slashOfMemGamma0
    {M : ℕ} (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Gamma1 M) k) :
    CuspForm.heckeTLinOne k hℓ hℓM (CuspForm.slashOfMemGamma0 M k hγ f) =
      CuspForm.slashOfMemGamma0 M k hγ (CuspForm.heckeTLinOne k hℓ hℓM f) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeTLinOne_slashOfMemGamma0.solution
