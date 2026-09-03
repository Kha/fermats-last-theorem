import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_CuspForm_exists_degeneracy_Gamma0

theorem CuspForm.exists_degeneracy_Gamma0 {k : ℤ} {M N d : ℕ} [NeZero N] (hd : d * M ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_degeneracy_Gamma0.solution
