import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

theorem AlgebraicCurve.Place.eq_of_comap_eq_of_forall_mem_nonunits_iff
    {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
    {κ' : Type*} [Field κ'] [Algebra κ κ'] [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']
    {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
    [IsScalarTower κ F F'] [IsScalarTower κ κ' F'] [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap κ' F')) = ⊤)
    (P : Place κ F) (W₁ W₂ : Place κ' F')
    (h₁ : W₁.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (h₂ : W₂.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (hc : ∀ x ∈ Subring.closure
        ((algebraMap F F') '' (P.toValuationSubring : Set F) ∪ Set.range (algebraMap κ' F')),
      x ∈ W₁.toValuationSubring.nonunits ↔ x ∈ W₂.toValuationSubring.nonunits) :
    W₁ = W₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff.solution
