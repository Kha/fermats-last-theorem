import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronPrimaryTorsionFFModels_exists_natCard_withConv_hffBarQ_algHom_eq_pow
attribute [-instance] GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod
open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring
theorem ModularCurve.JZeroNeronPrimaryTorsionFFModels.exists_natCard_withConv_hffBarQ_algHom_eq_pow
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (F : JZeroNeronPrimaryTorsionFFModels p q A hA C)
    (m : ℕ) (hqp : q ≠ p) :
    ∃ n : ℕ, Nat.card (WithConv (F.HffBarQ m hqp →ₐ[ZMod q] AlgebraicClosure (ZMod q))) = q ^ n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFFModels_exists_natCard_withConv_hffBarQ_algHom_eq_pow.solution
