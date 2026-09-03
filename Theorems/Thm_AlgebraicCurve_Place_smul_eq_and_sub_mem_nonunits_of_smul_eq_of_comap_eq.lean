import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_smul_eq_and_sub_mem_nonunits_of_smul_eq_of_comap_eq

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

theorem AlgebraicCurve.Place.smul_eq_and_sub_mem_nonunits_of_smul_eq_of_comap_eq
    {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
    {κ' : Type*} [Field κ'] [Algebra κ κ']
    {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
    [IsScalarTower κ F F'] [IsScalarTower κ κ' F']
    (σ : F ≃ₐ[κ] F) (σ' : F' ≃ₐ[κ'] F')
    (hσ : ∀ f : F, σ' (algebraMap F F' f) = algebraMap F F' (σ f))
    (P : Place κ F) (P' : Place κ' F')
    (hP' : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (hrat : ∀ x : F', x ∈ P'.toValuationSubring →
      ∃ c : κ', x - algebraMap κ' F' c ∈ P'.toValuationSubring.nonunits)
    (hfix : σ' • P' = P') :
    σ • P = P ∧ ∀ e : F, e ∈ P.toValuationSubring → σ e - e ∈ P.toValuationSubring.nonunits := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_smul_eq_and_sub_mem_nonunits_of_smul_eq_of_comap_eq.solution
