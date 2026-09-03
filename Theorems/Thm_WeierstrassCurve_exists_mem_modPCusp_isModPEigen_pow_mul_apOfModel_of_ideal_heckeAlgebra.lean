import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra
set_option autoImplicit false
open CuspForm ModPForms

theorem WeierstrassCurve.exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ)
    (N' : ℕ) [NeZero N'] (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (k : ℤ) (hk : 2 ≤ k) (hint : HasIntegralStructure N' k) (i : ℕ)
    (𝔪ₖ : Ideal (heckeAlgebra N' k S₀)) (h𝔪ₖ : 𝔪ₖ.IsMaximal)
    (hp𝔪ₖ : (p : heckeAlgebra N' k S₀) ∈ 𝔪ₖ)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        heckeAlgebra.T hℓ hℓN hℓS -
          ((ℓ ^ i * W.apOfModel ℓ : ℤ) : heckeAlgebra N' k S₀) ∈ 𝔪ₖ) :
    ∃ (φ : PowerSeries (AlgebraicClosure (ZMod p))) (lam : ℕ → AlgebraicClosure (ZMod p)),
      φ ∈ modPCusp N' k (AlgebraicClosure (ZMod p)) ∧ IsModPEigen N' S₀ k φ lam ∧
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
          lam ℓ = ((ℓ ^ i * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra.solution
