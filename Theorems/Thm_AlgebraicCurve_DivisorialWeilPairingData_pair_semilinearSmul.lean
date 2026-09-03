import Mathlib
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul
set_option autoImplicit false

theorem AlgebraicCurve.DivisorialWeilPairingData.pair_semilinearSmul {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n]
    [HasPrincipalDivisors K F]
    (e : DivisorialWeilPairingData K F n) (g : SemilinearAut K F)
    (x y : Pic0.torsion K F n) :
    e.pair (g • x) (g • y) = SemilinearAut.baseAut g (e.pair x y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul.solution
