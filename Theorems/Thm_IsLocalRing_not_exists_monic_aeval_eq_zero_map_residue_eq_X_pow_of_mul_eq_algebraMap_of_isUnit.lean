import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nakayama
import P2M.Util
import P2M.Sol.S_IsLocalRing_not_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_mul_eq_algebraMap_of_isUnit

set_option autoImplicit false

open Polynomial IsLocalRing

theorem IsLocalRing.not_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_mul_eq_algebraMap_of_isUnit
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {F : Type} [CommRing F] [Nontrivial F] [Algebra 𝒪 F]
    (x y : F) (hy : IsIntegral 𝒪 y) (u : 𝒪) (hu : IsUnit u)
    (hxy : x * y = algebraMap 𝒪 F u) :
    ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C 0) ^ R.natDegree) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_not_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_mul_eq_algebraMap_of_isUnit.solution
