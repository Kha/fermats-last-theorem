import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_of_integers_eq

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_algEquiv_of_integers_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fb₁ Fb₂ : Type*} [Field Fb₁] [Field Fb₂]
    [Algebra (IsLocalRing.ResidueField A) Fb₁] [Algebra (IsLocalRing.ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    (heq : R₁.integers = R₂.integers) :
    Nonempty (Fb₁ ≃ₐ[IsLocalRing.ResidueField A] Fb₂) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_of_integers_eq.solution
