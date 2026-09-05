module

public import Theorems.Thm_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord
public import Theorems.Thm_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord
import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) :=
  le_antisymm
    (Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord x hx D hD)
    (Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord x hx D hD)
