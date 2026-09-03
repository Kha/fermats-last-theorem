import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
namespace P2MW.S_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic
set_option Elab.async false

theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K] {x : L} (hx : IsAlgebraic K x) :
    x ∈ (algebraMap K L).range :=
  minpoly.degree_eq_one_iff.mp
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hx.isIntegral))

#print axioms solution
