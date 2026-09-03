import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_TaylorWiles_exists_isTaylorWilesPrime_of_statement

open NumberField FrobeniusDensity
theorem TaylorWiles.exists_isTaylorWilesPrime_of_statement
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜]
    (ρ : TaylorWiles.ResidualRep L 𝕜) (p n : ℕ) (hstmt : FrobeniusDensity.Statement L)
    {S : Finset ℕ} (seed : TaylorWiles.Seed ρ p n S) (T : Finset ℕ) :
    ∃ q : ℕ, q ∉ S ∧ q ∉ T ∧ TaylorWiles.IsTaylorWilesPrime ρ p n q := by p2m_exact_reverting @_root_.P2MW.S_TaylorWiles_exists_isTaylorWilesPrime_of_statement.solution
