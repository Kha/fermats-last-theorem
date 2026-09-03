import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_exists_twoEnd_of_modulus_ne_zero

set_option autoImplicit false

theorem AlgebraicCurve.Annulus.exists_twoEnd_of_modulus_ne_zero
    {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F] [Algebra K F]
    (An : Annulus A F) (hmod : ((An.modulus : K)) ≠ 0) (hz : An.param ≠ 0) :
    ∃ An' : Annulus A F, An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      An'.param * An.param = algebraMap K F ((An.modulus : K)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_exists_twoEnd_of_modulus_ne_zero.solution
