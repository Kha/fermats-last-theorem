import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq
    {N : ℕ} [NeZero N] {k : ℤ} [DecidableEq (DirichletCharacter ℂ N)] {ι : Type*} (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ N) (g : ι → CuspForm (Gamma1 N) k)
    (hg : ∀ i ∈ s, CuspForm.HasNebentypus (χ i) (g i))
    {ε : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) k} (hf : CuspForm.HasNebentypus ε f)
    (hsum : ∑ i ∈ s, g i = f) :
    ∑ i ∈ s.filter (fun i => χ i = ε), g i = f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq.solution
