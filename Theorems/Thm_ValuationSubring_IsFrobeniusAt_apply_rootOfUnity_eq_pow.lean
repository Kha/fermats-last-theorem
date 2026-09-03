import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow
attribute [-simp] WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
theorem ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q)
    (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ p = 1) :
    σ ζ = ζ ^ q := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow.solution
