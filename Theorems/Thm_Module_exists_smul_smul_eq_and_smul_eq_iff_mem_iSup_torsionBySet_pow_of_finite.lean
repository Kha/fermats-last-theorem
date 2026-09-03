import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite

theorem Module.exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (N : Submodule T M) [Finite ↥N] (𝔓 : Ideal T) :
    ∃ t : T, (∀ x ∈ N, t • (t • x) = t • x) ∧
      ∀ x ∈ N, (t • x = x ↔ x ∈ ⨆ k : ℕ, Submodule.torsionBySet T M (↑(𝔓 ^ k) : Set T)) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite.solution
