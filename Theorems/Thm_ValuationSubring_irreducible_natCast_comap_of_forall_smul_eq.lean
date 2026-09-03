import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_irreducible_natCast_comap_of_forall_smul_eq

open scoped Pointwise
theorem ValuationSubring.irreducible_natCast_comap_of_forall_smul_eq (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    (V : ValuationSubring N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ((ℓ : ℕ) : N) ∈ V.nonunits)
    (E : IntermediateField ℚ N)
    (hE : ∀ τ : N ≃ₐ[ℚ] N, τ • V = V → ∀ x ∈ E, τ x = x) :
    Irreducible ((ℓ : ℕ) : V.comap (algebraMap E N)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_irreducible_natCast_comap_of_forall_smul_eq.solution
