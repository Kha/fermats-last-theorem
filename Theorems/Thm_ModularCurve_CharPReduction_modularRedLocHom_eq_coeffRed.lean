import Definitions.Def_ModularCurve_CharPReduction
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed

open ModularCurve CharPReduction
theorem ModularCurve.CharPReduction.modularRedLocHom_eq_coeffRed {L : Type*} [CommRing L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (N : ℕ) [NeZero N]
    (f : modularLocalized N A red) (hf : (f : LaurentSeries L) ∈ integralCoeffs A) :
    modularRedLocHom N A red f = coeffRed A red ⟨(f : LaurentSeries L), hf⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed.solution
