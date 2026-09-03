import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_nonempty_tateModule_basis_of_abelJacobiCard

theorem ModularCurve.JZero.nonempty_tateModule_basis_of_abelJacobiCard :
    ∀ (N p g : ℕ) (hp : p.Prime),
      haveI : Fact p.Prime := ⟨hp⟩
      AlgebraicCurve.AbelJacobiCard (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) p g →
        Nonempty (Module.Basis (Fin (2 * g)) ℤ_[p] (TateModule p (ModularCurve.JZero N))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_nonempty_tateModule_basis_of_abelJacobiCard.solution
