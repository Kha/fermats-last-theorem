import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import P2M.Util
import P2M.Sol.S_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute

theorem Module.End.exists_forall_apply_eq_smul_of_pairwise_commute
    {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute.solution
