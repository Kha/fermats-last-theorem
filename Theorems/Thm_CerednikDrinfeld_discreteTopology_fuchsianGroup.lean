import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_discreteTopology_fuchsianGroup

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.discreteTopology_fuchsianGroup {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    DiscreteTopology ↥(fuchsianGroup R ι) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_discreteTopology_fuchsianGroup.solution
