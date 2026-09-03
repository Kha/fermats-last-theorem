import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_not_isCusp_fuchsianGroup_of_forall_isUnit

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.not_isCusp_fuchsianGroup_of_forall_isUnit {a b : ℚ}
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (hι : Function.Injective ι) (c : OnePoint ℝ) :
    ¬ IsCusp c (fuchsianGroup R ι) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_not_isCusp_fuchsianGroup_of_forall_isUnit.solution
