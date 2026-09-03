import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_veluQuotient_descent_of_smul_mem_zmultiples

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.exists_veluQuotient_descent_of_smul_mem_zmultiples
    {W : WeierstrassCurve ℚ} {Q : (W⁄(AlgebraicClosure ℚ)).toAffine.Point} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hord : addOrderOf Q = p)
    (hstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q ∈ AddSubgroup.zmultiples Q) :
    ∃ V₀ : WeierstrassCurve ℚ,
      V₀.map (algebraMap ℚ (AlgebraicClosure ℚ))
        = (W⁄(AlgebraicClosure ℚ)).veluQuotient
            ((W⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q ((p - 1) / 2)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_veluQuotient_descent_of_smul_mem_zmultiples.solution
