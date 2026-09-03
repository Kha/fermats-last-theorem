import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

theorem RingHom.isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow
    {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (σ₀ σ₁ : A →+* B) (ι₀ ι₁ : B → A)
    (h₀ : ∀ b, σ₀ (ι₀ b) = b) (h₁ : ∀ b, σ₁ (ι₁ b) = b)
    (p : ℕ) (hp : 2 ≤ p) (h₀₁ : ∀ b, ∃ c, σ₀ (ι₁ b) = c ^ p) :
    IsReduced (A ⧸ (RingHom.ker σ₀ ⊔ RingHom.ker σ₁)) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow.solution
