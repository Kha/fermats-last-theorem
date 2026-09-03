import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two
open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p 2 A hA C m) (i : Fin flag.n) :
    ∃ da : ℕ,
      Nat.card (flag.G i.succ →ₐ[ℤ] AlgebraicClosure (ZMod 2))
        = 2 ^ da * Nat.card (flag.G i.castSucc →ₐ[ℤ] AlgebraicClosure (ZMod 2)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two.solution
