import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
namespace P2MW.S_CuspForm_heckeAlgebra_ringHom_ext_of_primeFactors_subset

theorem solution {N : ℕ} [NeZero N] {S : Set ℕ}
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    {R : Type} [CommRing R]
    (θ₁ θ₂ : CuspForm.heckeAlgebra N 2 S →+* R)
    (h : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = θ₂ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) :
    θ₁ = θ₂ := by
  apply RingHom.toIntAlgHom_injective
  refine AlgHom.ext_of_eq_adjoin (S := CuspForm.heckeAlgebra N 2 S)
    (s := CuspForm.heckeGenerators N 2 S) rfl fun x hx => ?_
  rcases hx with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
  · exact h ℓ hℓ hℓN hℓS
  · exact absurd (hNS q hq hqN) hqS
