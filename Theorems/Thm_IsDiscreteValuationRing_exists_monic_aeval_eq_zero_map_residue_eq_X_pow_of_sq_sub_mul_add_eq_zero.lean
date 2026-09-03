import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero

set_option autoImplicit false

open Polynomial IsLocalRing

theorem IsDiscreteValuationRing.exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {F : Type} [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (ϖ : 𝒪) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal 𝒪) (a x : F)
    (ha : (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval a R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C 0) ^ R.natDegree))
    (hx : x * x - a * x + algebraMap 𝒪 F ϖ = 0) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C 0) ^ R.natDegree) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero.solution
