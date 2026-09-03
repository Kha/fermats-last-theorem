import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.IsFrobeniusEndo.restrictAlong_injective {K F : Type*} [Field K] [Field F] [Algebra K F] {φ : F →ₐ[K] F} {ℓ : ℕ} (h : AlgebraicCurve.IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0) (hφ : φ.IsIntegral) : Function.Injective (AlgebraicCurve.Place.restrictAlong φ hφ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.IsFrobeniusEndo.restrictAlong_injective AlgebraicCurve.IsFrobeniusEndo.restrictAlong_injective
