import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_TaylorWiles_exists_isTaylorWilesPrime_of_statement
import P2M.Util
namespace P2MW.S_TaylorWiles_exists_isTaylorWilesPrime
attribute [-instance] FrobeniusDensity.liesOver_ratBelow

open NumberField FrobeniusDensity

theorem solution {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜]
    (ρ : TaylorWiles.ResidualRep L 𝕜) (p n : ℕ)
    {S : Finset ℕ} (seed : TaylorWiles.Seed ρ p n S) (T : Finset ℕ) :
    ∃ q : ℕ, q ∉ S ∧ q ∉ T ∧ TaylorWiles.IsTaylorWilesPrime ρ p n q :=
  TaylorWiles.exists_isTaylorWilesPrime_of_statement ρ p n (FrobeniusDensity.statement L) seed T
