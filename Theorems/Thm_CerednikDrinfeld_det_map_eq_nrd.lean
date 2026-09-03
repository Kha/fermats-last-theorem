import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_det_map_eq_nrd

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.det_map_eq_nrd {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (x : ℍ[ℚ, a, b]) : (ι x).det = ((nrd x : ℚ) : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_det_map_eq_nrd.solution
