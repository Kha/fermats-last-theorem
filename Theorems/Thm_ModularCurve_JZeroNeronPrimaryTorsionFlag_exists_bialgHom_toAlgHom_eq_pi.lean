import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_bialgHom_toAlgHom_eq_pi
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin (flag.n + 1)) :
    ∃ πc : C.H m →ₐc[ℤ] flag.G i, (πc : C.H m →ₐ[ℤ] flag.G i) = flag.π i := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi.solution
