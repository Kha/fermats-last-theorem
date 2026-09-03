import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_det_eq_nrd_of_injective

set_option autoImplicit false

open scoped MatrixGroups Quaternion
open QuaternionAlgebra CerednikDrinfeld
theorem QuaternionAlgebra.det_eq_nrd_of_injective
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (x : ℍ[ℚ, a, b]) :
    (ι x).det = ((nrd x : ℚ) : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_det_eq_nrd_of_injective.solution
