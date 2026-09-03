import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FiniteType_exists_prime_charP_residueField_of_isMaximal_of_faithfullyFlat

set_option autoImplicit false

theorem Algebra.FiniteType.exists_prime_charP_residueField_of_isMaximal_of_faithfullyFlat
    {S : Type} [CommRing S] [Algebra.FiniteType ℤ S] (𝔭 : PrimeSpectrum S) (h𝔪 : 𝔭.asIdeal.IsMaximal)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra S R] [Algebra (Localization.AtPrime 𝔭.asIdeal) R]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) R]
    (hff : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) R) :
    ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField R) p := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FiniteType_exists_prime_charP_residueField_of_isMaximal_of_faithfullyFlat.solution
