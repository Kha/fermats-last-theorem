module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_Repartitions
public import Definitions.Def_AlgebraicCurve_IsCurveOver
public import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord

@[expose] public section

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D ≤ (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord.solution
