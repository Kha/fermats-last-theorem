import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem NumberField.SUnits.algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
    (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (u : (↥F)ˣ) (hu : u ∈ NumberField.SUnits.sUnits ℚ ↥F Sℚ)
    (q : Nat.Primes) (hq : q ∉ S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime (q : ℕ)) :
    algebraMap ↥F (AlgebraicClosure ℚ) (u : ↥F) ∈ A ∧ (algebraMap ↥F (AlgebraicClosure ℚ) (u : ↥F))⁻¹ ∈ A := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime.solution
