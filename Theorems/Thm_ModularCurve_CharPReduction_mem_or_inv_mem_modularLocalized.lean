import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPReduction_mem_or_inv_mem_modularLocalized

open ModularCurve CharPReduction
theorem ModularCurve.CharPReduction.mem_or_inv_mem_modularLocalized {L : Type*} [Field L] (A : ValuationSubring L)
    {k : Type*} [Field k] (red : A.toSubring →+* k) (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    {f : LaurentSeries L}
    (hf : f ∈ IntermediateField.adjoin L {jqModC L, jqNModC L N}) :
    f ∈ modularLocalized N A.toSubring red ∨ f⁻¹ ∈ modularLocalized N A.toSubring red := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPReduction_mem_or_inv_mem_modularLocalized.solution
