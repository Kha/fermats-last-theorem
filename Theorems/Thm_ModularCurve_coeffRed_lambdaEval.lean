import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_CharPReduction
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffRed_lambdaEval
set_option autoImplicit false

open ModularCurve ModularCurve.LambdaNodeLocalized ModularCurve.CharPReduction

theorem ModularCurve.coeffRed_lambdaEval (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (p : MvPolynomial (Fin 2) A) :
    ∃ hp : LambdaNodeLocalized.lambdaEval N A p ∈ CharPReduction.integralCoeffs A,
      CharPReduction.coeffRed A red ⟨LambdaNodeLocalized.lambdaEval N A p, hp⟩
        = MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![lambdaModC k, lambdaNModC k N] p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffRed_lambdaEval.solution
