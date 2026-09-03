import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two

set_option autoImplicit false

open CuspForm

theorem WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ)
    (N' : ℕ) [NeZero N']
    (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (hS₀N : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S₀)
    (𝔪ₖ : Ideal (heckeAlgebra N' 2 S₀)) (h𝔪ₖ : 𝔪ₖ.IsMaximal)
    (hp𝔪ₖ : (p : heckeAlgebra N' 2 S₀) ∈ 𝔪ₖ)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        heckeAlgebra.T hℓ hℓN hℓS -
          ((W.apOfModel ℓ : ℤ) : heckeAlgebra N' 2 S₀) ∈ 𝔪ₖ) :
    ∃ 𝔪₂ : Ideal (heckeAlgebra (N' * p) 2 S₀), 𝔪₂.IsMaximal ∧
      (p : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N' * p),
        W.IsGoodPrimeFor ℓ →
          heckeAlgebra.T hℓ hℓN hℓS -
            ((W.apOfModel ℓ : ℤ) : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two.solution
