import Definitions.Def_ModularCurve_FibreModel
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_FibreModel_red_surjective

set_option autoImplicit false

open ModularCurve.CharPModel in
theorem ModularCurve.CharPModel.FibreModel.red_surjective
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ]
    (red : A →+* k) (fm : FibreModel N A ℓ k red) :
    Function.Surjective red := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_FibreModel_red_surjective.solution
