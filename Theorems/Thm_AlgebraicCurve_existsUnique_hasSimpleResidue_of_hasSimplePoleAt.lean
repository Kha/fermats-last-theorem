import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) (hω : v.HasSimplePoleAt ω) :
    ∃! a : K, v.HasSimpleResidue ω a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt.solution
