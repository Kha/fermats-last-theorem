module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
import P2M.Util

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  ⟨fun f hf =>
    ⟨Finsupp.ofSupportFinite (fun v : Place K (RatFunc K) => v.ord f)
        (AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero hf),
      fun _ => rfl,
      AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord _ fun _ => rfl⟩⟩
end S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.solution
end
