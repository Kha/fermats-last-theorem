import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_eq_of_monic_aeval_eq_zero_map_residue_eq_pow

set_option autoImplicit false

open Polynomial IsLocalRing

theorem IsDiscreteValuationRing.eq_of_monic_aeval_eq_zero_map_residue_eq_pow
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {F : Type} [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (x : F) (c c' : IsLocalRing.ResidueField 𝒪)
    (R : Polynomial 𝒪) (hR : R.Monic) (hRx : Polynomial.aeval x R = 0)
    (hRc : R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree)
    (R' : Polynomial 𝒪) (hR' : R'.Monic) (hR'x : Polynomial.aeval x R' = 0)
    (hR'c : R'.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c') ^ R'.natDegree) :
    c = c' := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_eq_of_monic_aeval_eq_zero_map_residue_eq_pow.solution
