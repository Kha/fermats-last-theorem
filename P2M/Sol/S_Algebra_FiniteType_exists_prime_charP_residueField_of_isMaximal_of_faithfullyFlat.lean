import Mathlib
import Theorems.Thm_Algebra_FiniteType_finite_quotient_and_exists_charP_of_isMaximal_int
import P2M.Util
namespace P2MW.S_Algebra_FiniteType_exists_prime_charP_residueField_of_isMaximal_of_faithfullyFlat

set_option autoImplicit false

theorem solution
    {S : Type} [CommRing S] [Algebra.FiniteType ℤ S] (𝔭 : PrimeSpectrum S) (h𝔪 : 𝔭.asIdeal.IsMaximal)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra S R] [Algebra (Localization.AtPrime 𝔭.asIdeal) R]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) R]
    (hff : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) R) :
    ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField R) p := by
  haveI := h𝔪
  obtain ⟨-, p, hp, hchar⟩ := Algebra.FiniteType.finite_quotient_and_exists_charP_of_isMaximal_int S 𝔭.asIdeal
  refine ⟨p, hp, ?_⟩

  have h1 : (p : S) ∈ 𝔭.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (S ⧸ 𝔭.asIdeal) p

  have h2 : (p : Localization.AtPrime 𝔭.asIdeal) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭.asIdeal) := by
    rw [← map_natCast (algebraMap S (Localization.AtPrime 𝔭.asIdeal)) p]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭.asIdeal) 𝔭.asIdeal (p : S)).mpr h1

  have h3 : (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭.asIdeal)).map
      (algebraMap (Localization.AtPrime 𝔭.asIdeal) R) ≠ ⊤ := by
    intro htop
    apply hff.submodule_ne_top (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime 𝔭.asIdeal))
    rw [Ideal.smul_top_eq_map, htop, Submodule.restrictScalars_top]

  have h4 : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    apply IsLocalRing.le_maximalIdeal h3
    rw [← map_natCast (algebraMap (Localization.AtPrime 𝔭.asIdeal) R) p]
    exact Ideal.mem_map_of_mem _ h2

  rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (IsLocalRing.residue R) p, IsLocalRing.residue_eq_zero_iff]
  exact h4
