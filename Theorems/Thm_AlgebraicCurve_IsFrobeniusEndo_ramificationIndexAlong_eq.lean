import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.IsFrobeniusEndo.ramificationIndexAlong_eq {K F : Type*} [Field K] [Field F] [Algebra K F] {φ : F →ₐ[K] F} {ℓ : ℕ} (h : AlgebraicCurve.IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0) (w : AlgebraicCurve.Place K F) : AlgebraicCurve.Place.ramificationIndexAlong φ w = ℓ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.IsFrobeniusEndo.ramificationIndexAlong_eq AlgebraicCurve.IsFrobeniusEndo.ramificationIndexAlong_eq
