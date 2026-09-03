import Definitions.Def_ModularCurve_CharPReduction
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPReduction_exists_modularRedLocHom_eq

open ModularCurve CharPReduction
theorem ModularCurve.CharPReduction.exists_modularRedLocHom_eq {L : Type*} [Field L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (N : ℕ) [NeZero N]
    (hred : Function.Surjective red)
    {y : LaurentSeries k} (hy : y ∈ modularFunctionFieldC k N) :
    ∃ f : modularLocalized N A red, modularRedLocHom N A red f = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPReduction_exists_modularRedLocHom_eq.solution
