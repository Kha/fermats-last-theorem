import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow
open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring
theorem ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ) :
    ∃ a : ℕ, Nat.card (C.H m →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow.solution
