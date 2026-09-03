import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_heckeAlgebra_ringHom_ext_of_primeFactors_subset

theorem CuspForm.heckeAlgebra_ringHom_ext_of_primeFactors_subset {N : ℕ} [NeZero N] {S : Set ℕ}
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    {R : Type} [CommRing R]
    (θ₁ θ₂ : CuspForm.heckeAlgebra N 2 S →+* R)
    (h : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = θ₂ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) :
    θ₁ = θ₂ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeAlgebra_ringHom_ext_of_primeFactors_subset.solution
