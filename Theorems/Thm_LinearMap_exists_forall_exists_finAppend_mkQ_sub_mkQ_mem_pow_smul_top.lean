import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type v} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    (F E : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (ε : ∀ k, F k →ₗ[B] E k) (ψE : ∀ k, GE →ₗ[B] E k) (lam : ∀ k, GK →ₗ[B] F k)
    (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (hlami : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (lam (k + c)) ≤ J ^ (k + 1) • (⊤ : Submodule B GK))
    {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] GE) (hp₁ : Function.Surjective p₁)
    (p₂ : (Fin r₂ → B) →ₗ[B] GE) (hp₂ : Function.Surjective p₂)
    (P : (Fin (r₁ + r₂) → B) →ₗ[B] GE) (hP : ∀ (v : Fin r₁ → B) (w : Fin r₂ → B), P (Fin.append v w) = p₁ v + p₂ w) :
    ∃ c : ℕ, ∀ (n : ℕ)
      (ℓ₁ : (Fin r₁ → B) →ₗ[B] F (n + c)) (_ : ε (n + c) ∘ₗ ℓ₁ = ψE (n + c) ∘ₗ p₁)
      (ℓ₂ : (Fin r₂ → B) →ₗ[B] F (n + c)) (_ : ε (n + c) ∘ₗ ℓ₂ = ψE (n + c) ∘ₗ p₂)
      (δ₁ : ↥(LinearMap.ker p₁) →ₗ[B] GK) (_ : lam (n + c) ∘ₗ δ₁ = ℓ₁ ∘ₗ (LinearMap.ker p₁).subtype)
      (δ₂ : ↥(LinearMap.ker p₂) →ₗ[B] GK) (_ : lam (n + c) ∘ₗ δ₂ = ℓ₂ ∘ₗ (LinearMap.ker p₂).subtype),
      ∃ δ₁' δ₂' : ↥(LinearMap.ker P) →ₗ[B] GK,
        (∀ (s : ↥(LinearMap.ker p₁)) (hs : Fin.append (s : Fin r₁ → B) (0 : Fin r₂ → B) ∈ LinearMap.ker P),
          δ₁' ⟨Fin.append (s : Fin r₁ → B) 0, hs⟩ = δ₁ s) ∧
        (∀ (s : ↥(LinearMap.ker p₂)) (hs : Fin.append (0 : Fin r₁ → B) (s : Fin r₂ → B) ∈ LinearMap.ker P),
          δ₂' ⟨Fin.append 0 (s : Fin r₂ → B), hs⟩ = δ₂ s) ∧
        Submodule.Quotient.mk δ₁' - Submodule.Quotient.mk δ₂' ∈
          J ^ (n + 1) • (⊤ : Submodule B ((↥(LinearMap.ker P) →ₗ[B] GK) ⧸
            LinearMap.range (LinearMap.lcomp B GK (LinearMap.ker P).subtype))) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_exists_finAppend_mkQ_sub_mkQ_mem_pow_smul_top.solution
