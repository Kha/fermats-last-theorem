import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.FieldTheory.Relrank
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.CharPModel.relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm
    (N : ℕ) [NeZero N] (k : Type*) [Field k]
    (data : ModularPolynomialData N) (hsym : EvalSymm data.Φ)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N) :
    (IntermediateField.adjoin k {(jqNModC k N : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm.solution
