import Mathlib
import Definitions.Def_EllipticCurve_PointReduction
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_reducePoint_add

theorem WeierstrassCurve.reducePoint_add
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    [DecidableEq (IsLocalRing.ResidueField R)]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] (P Q : W.toAffine.Point) :
    WeierstrassCurve.reducePoint_alt R W (P + Q)
      = WeierstrassCurve.reducePoint_alt R W P + WeierstrassCurve.reducePoint_alt R W Q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_reducePoint_add.solution
