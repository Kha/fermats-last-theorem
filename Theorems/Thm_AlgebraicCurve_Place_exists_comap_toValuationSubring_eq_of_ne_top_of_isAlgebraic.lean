import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic
    {κ : Type*} [Field κ] {k : Type*} [Field k] {E : Type*} [Field E]
    [Algebra κ k] [Algebra k E] [Algebra κ E] [IsScalarTower κ k E] [Algebra.IsAlgebraic k E]
    (x : E) [FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set E)) E]
    (W : ValuationSubring k) (hW : W ≠ ⊤) (hκ : ∀ a : κ, algebraMap κ k a ∈ W) :
    ∃ w : AlgebraicCurve.Place κ E, w.toValuationSubring.comap (algebraMap k E) = W := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic.solution
