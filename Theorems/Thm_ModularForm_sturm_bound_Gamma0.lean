import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_ModularForm_sturm_bound_Gamma0

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.sturm_bound_Gamma0 (N : ℕ) [NeZero N] {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (h : ∀ n : ℕ, n ≤ (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 → (qExpansion 1 f).coeff n = 0) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_sturm_bound_Gamma0.solution
