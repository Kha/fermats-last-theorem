import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_finset_forall_nrd_eq_exists_mul_unit

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_finset_forall_nrd_eq_exists_mul_unit {a b : ℚ}
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (n : ℚ) :
    ∃ T : Finset ℍ[ℚ, a, b], (↑T : Set ℍ[ℚ, a, b]) ⊆ R ∧
      ∀ r ∈ R, nrd r = n → ∃ t ∈ T, ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ r = t * u := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_finset_forall_nrd_eq_exists_mul_unit.solution
