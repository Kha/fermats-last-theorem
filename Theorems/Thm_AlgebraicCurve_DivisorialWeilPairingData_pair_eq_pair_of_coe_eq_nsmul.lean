import Mathlib
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_DivisorialWeilPairingData_pair_eq_pair_of_coe_eq_nsmul
set_option autoImplicit false

theorem AlgebraicCurve.DivisorialWeilPairingData.pair_eq_pair_of_coe_eq_nsmul {K F : Type*} [Field K] [Field F] [Algebra K F]
    (m n : ℕ) [NeZero m] [NeZero (m * n)] [HasPrincipalDivisors K F]
    (e_mn : DivisorialWeilPairingData K F (m * n))
    (e_m : DivisorialWeilPairingData K F m)
    (x : Pic0.torsion K F (m * n)) (y : Pic0.torsion K F m)
    (y' : Pic0.torsion K F (m * n)) (hy : (y' : Pic0 K F) = (y : Pic0 K F))
    (x' : Pic0.torsion K F m) (hx : (x' : Pic0 K F) = (n : ℤ) • (x : Pic0 K F)) :
    e_mn.pair x y' = e_m.pair x' y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_pair_eq_pair_of_coe_eq_nsmul.solution
