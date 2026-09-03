import Definitions.Def_TaylorWiles_Primes
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Fixed
import Mathlib.GroupTheory.GroupAction.Quotient
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed

open NumberField Ideal
theorem FrobeniusDensity.ncard_degreeOne_primesOver_eq_ncard_frobFixed
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {H : Subgroup (L ≃ₐ[ℚ] L)} {E : IntermediateField ℚ L} [IsGaloisGroup H E L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime]
    [Q₀.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    haveI : Finite ((𝓞 L) ⧸ Q₀) :=
      FrobeniusDensity.finite_quotient_of_ne_bot
        (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    {𝔮 ∈ (FrobeniusDensity.ratPrimeIdeal ℓ).primesOver (𝓞 E) |
      Nat.card ((𝓞 E) ⧸ 𝔮) = ℓ}.ncard
      = {x : (L ≃ₐ[ℚ] L) ⧸ H | arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀ • x = x}.ncard := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed.solution
