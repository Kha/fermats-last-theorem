module

public import Mathlib
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import P2M.Util
public import P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg

@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (t : F) (ht : Transcendental K t) [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F] [AlgebraicCurve.HasPrincipalDivisors K F] (z : F) (hz : ∀ v : AlgebraicCurve.Place K F, 0 ≤ v.ord t → 0 ≤ v.ord z) : IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.solution
