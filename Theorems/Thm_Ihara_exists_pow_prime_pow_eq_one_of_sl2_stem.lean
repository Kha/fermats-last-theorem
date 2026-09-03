import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center
import P2M.Util
import P2M.Sol.S_Ihara_exists_pow_prime_pow_eq_one_of_sl2_stem

open scoped MatrixGroups in
theorem Ihara.exists_pow_prime_pow_eq_one_of_sl2_stem (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {E : Type} [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
    (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {x : E} (hx : x ∈ π.ker)
    (hxcomm : x ∈ commutator E) :
    ∃ k : ℕ, x ^ q ^ k = 1 := by p2m_exact_reverting @_root_.P2MW.S_Ihara_exists_pow_prime_pow_eq_one_of_sl2_stem.solution
