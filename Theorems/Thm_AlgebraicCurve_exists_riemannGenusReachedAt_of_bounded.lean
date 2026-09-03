import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_riemannGenusReachedAt_of_bounded

namespace AlgebraicCurve
theorem exists_riemannGenusReachedAt_of_bounded {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_riemannGenusReachedAt_of_bounded.solution
end AlgebraicCurve
