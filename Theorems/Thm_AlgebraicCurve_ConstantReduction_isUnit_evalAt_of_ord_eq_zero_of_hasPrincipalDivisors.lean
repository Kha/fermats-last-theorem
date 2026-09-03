import Definitions.Def_ModularCurve_FinitePlaceLift
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ConstantReduction_isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors
    {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F] [Algebra K F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    {P : Place K F} (hP : P.IsRational) {f : F} (hf : f ∈ R.integers) (hres : R.residue ⟨f, hf⟩ ≠ 0)
    (hord : (R.placeMap P).ord (R.residue ⟨f, hf⟩) = 0)
    (hfib : ∀ w : Place K F, R.placeMap w = R.placeMap P → f ∈ w.toValuationSubring) :
    ∃ h : P.evalAt f ∈ A, IsUnit (⟨P.evalAt f, h⟩ : A) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors.solution
