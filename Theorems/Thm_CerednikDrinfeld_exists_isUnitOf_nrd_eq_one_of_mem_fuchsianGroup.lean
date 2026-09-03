import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_isUnitOf_nrd_eq_one_of_mem_fuchsianGroup

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open QuaternionAlgebra CerednikDrinfeld
theorem CerednikDrinfeld.exists_isUnitOf_nrd_eq_one_of_mem_fuchsianGroup
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ fuchsianGroup R ι) :
    ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ι u := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_isUnitOf_nrd_eq_one_of_mem_fuchsianGroup.solution
