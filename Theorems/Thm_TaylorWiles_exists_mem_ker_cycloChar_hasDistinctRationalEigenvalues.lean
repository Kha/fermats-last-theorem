import Mathlib
import Definitions.Def_TaylorWiles_CyclotomicChar
import P2M.Util
import P2M.Sol.S_TaylorWiles_exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues

open NumberField

theorem TaylorWiles.exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] {𝕜 : Type*} [Field 𝕜]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (ρ : TaylorWiles.ResidualRep L 𝕜) (n : ℕ)
    {ζ : 𝓞 L} [NeZero (p ^ n)] (hζ : IsPrimitiveRoot ζ (p ^ n))
    (h2 : (2 : 𝕜) ≠ 0)
    (hirr : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (hsplit : ∀ g : L ≃ₐ[ℚ] L, ∃ a b : 𝕜, (ρ g).trace = a + b ∧ (ρ g).det = a * b) :
    ∃ σ ∈ (TaylorWiles.cycloChar hζ).ker, (ρ σ).HasDistinctRationalEigenvalues := by p2m_exact_reverting @_root_.P2MW.S_TaylorWiles_exists_mem_ker_cycloChar_hasDistinctRationalEigenvalues.solution
