import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import P2M.Util
namespace P2MW.S_IsArtinianRing_finite_of_finite_residueField

theorem solution (R : Type*) [CommRing R] [IsArtinianRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)] :
    Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hn
  have h1 : Finite (R ⧸ IsLocalRing.maximalIdeal R) := ‹Finite (IsLocalRing.ResidueField R)›
  have h2 : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  rw [hn, Ideal.zero_eq_bot] at h2
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv
