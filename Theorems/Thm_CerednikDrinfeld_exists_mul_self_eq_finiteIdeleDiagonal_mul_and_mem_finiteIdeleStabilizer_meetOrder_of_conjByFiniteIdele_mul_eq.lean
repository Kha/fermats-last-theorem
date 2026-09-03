import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N) {q' : ℕ} [Fact q'.Prime] (hqq' : q' ≠ q)
    (hdef : IsDefiniteRamifiedExactlyAt a b q') (hnH : n ∈ primeHeckeSet R q)
    (hn : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n) :
    (∃ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n),
        n * n = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) * u) ∧
    (∀ u ∈ Submodule.finiteIdeleStabilizer R,
        Submodule.conjByFiniteIdele R (u * n) = Submodule.conjByFiniteIdele R n →
          u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq.solution
