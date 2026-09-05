module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_DivisorPushPull
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import Definitions.Def_AlgebraicCurve_PoleDivisorPackage
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_linearIndependent_pow_mul

@[expose] public section

namespace AlgebraicCurve
theorem linearIndependent_pow_mul {K : Type*} {E : Type*} {F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] {x : E} {n : ℕ} {u : Fin n → F}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) (hu : LinearIndependent E u) :
    LinearIndependent K (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_linearIndependent_pow_mul.solution
end AlgebraicCurve
