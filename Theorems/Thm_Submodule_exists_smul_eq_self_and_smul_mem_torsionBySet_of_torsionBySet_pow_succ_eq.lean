import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq

set_option autoImplicit false

theorem Submodule.exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite M]
    (I : Ideal R) (N : ℕ)
    (hN : Submodule.torsionBySet R M (↑(I ^ (N + 1)) : Set R) = Submodule.torsionBySet R M (↑(I ^ N) : Set R)) :
    ∃ t : R, (∀ v ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R), t • v = v) ∧
      ∀ m : M, t • m ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq.solution
