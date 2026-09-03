import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq

set_option autoImplicit false

open Polynomial IsLocalRing

theorem IsLocalRing.exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)]
    {F : Type} [CommRing F] [Algebra 𝒪 F]
    (φ : A →ₐ[𝒪] F) (x : A) (c : IsLocalRing.ResidueField 𝒪)
    (hx : IsLocalRing.residue A x = IsLocalRing.ResidueField.map (algebraMap 𝒪 A) c) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (φ x) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq.solution
