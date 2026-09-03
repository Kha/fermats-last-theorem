import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic

open ModularCurve CharPReduction
theorem ModularCurve.CharPReduction.mem_modularLocalized_of_eval2_monic {L : Type*} [Field L] (A : ValuationSubring L)
    {k : Type*} [Field k] (red : A.toSubring →+* k) (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    {x : LaurentSeries L}
    (hx : x ∈ IntermediateField.adjoin L {jqModC L, jqNModC L N})
    {p : Polynomial (modularLocalized N A.toSubring red)} (hp : p.Monic)
    (hev : Polynomial.eval₂ (modularLocalized N A.toSubring red).subtype x p = 0) :
    x ∈ modularLocalized N A.toSubring red := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic.solution
