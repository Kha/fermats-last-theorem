import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_smul_eq_of_comap_eq_of_forall_sub_mem_nonunits

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.smul_eq_of_comap_eq_of_forall_sub_mem_nonunits
    {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
    {κ' : Type*} [Field κ'] [Algebra κ κ'] [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']
    {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
    [IsScalarTower κ F F'] [IsScalarTower κ κ' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap κ' F')) = ⊤)
    (σ : F ≃ₐ[κ] F) (σ' : F' ≃ₐ[κ'] F')
    (hσ : ∀ f : F, σ' (algebraMap F F' f) = algebraMap F F' (σ f))
    (P : Place κ F) (hP : σ • P = P)
    (hI : ∀ e : F, e ∈ P.toValuationSubring → σ e - e ∈ P.toValuationSubring.nonunits)
    (P' : Place κ' F')
    (hP' : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) :
    σ' • P' = P' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_smul_eq_of_comap_eq_of_forall_sub_mem_nonunits.solution
