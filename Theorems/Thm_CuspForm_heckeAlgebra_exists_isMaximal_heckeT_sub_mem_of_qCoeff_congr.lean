import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_heckeAlgebra_exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr
set_option autoImplicit false
open CuspForm ModularFormClass

theorem CuspForm.heckeAlgebra.exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr (p : ℕ) [Fact p.Prime] (N' : ℕ) [NeZero N'] (k : ℤ) (S₀ : Set ℕ)
    (hS₀N : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S₀) (c : ℕ)
    (hc : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → ¬ ℓ ∣ c)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (G : CuspForm (CongruenceSubgroup.Gamma0 N') k)
    (hGint : ∀ n : ℕ, n.Coprime c → ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n)
    (hGne : ∃ (n : ℕ) (x y : integralClosure ℤ ℂ), n.Coprime c ∧ y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n ∧ x ∉ 𝔪)
    (a : ℕ → ℤ) (Q : ℕ → Prop)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      ∃ e : integralClosure ℤ ℂ, (Q ℓ → e - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪) ∧
        ∀ (n : ℕ) (x x' y : integralClosure ℤ ℂ), n.Coprime c → y ∉ 𝔪 →
          (x : ℂ) = y * qCoeff (((heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' k S₀) :
              Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k)) G) n →
          (x' : ℂ) = y * qCoeff G n → x - e * x' ∈ 𝔪) :
    ∃ 𝔪ₖ : Ideal (heckeAlgebra N' k S₀), 𝔪ₖ.IsMaximal ∧
      (p : heckeAlgebra N' k S₀) ∈ 𝔪ₖ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'), Q ℓ →
        heckeAlgebra.T hℓ hℓN hℓS - ((a ℓ : ℤ) : heckeAlgebra N' k S₀) ∈ 𝔪ₖ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeAlgebra_exists_isMaximal_heckeT_sub_mem_of_qCoeff_congr.solution
