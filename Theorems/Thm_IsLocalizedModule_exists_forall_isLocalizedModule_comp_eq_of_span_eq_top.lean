import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalizedModule_exists_forall_isLocalizedModule_comp_eq_of_span_eq_top

set_option autoImplicit false

universe u

theorem IsLocalizedModule.exists_forall_isLocalizedModule_comp_eq_of_span_eq_top
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (hM : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (LinearMap.id : M i →ₗ[B] M i))
    (M₂ : Fin k → Fin k → Type u) [∀ i j, AddCommGroup (M₂ i j)] [∀ i j, Module B (M₂ i j)]
    (ρl : ∀ i j, M i →ₗ[B] M₂ i j) (ρr : ∀ i j, M j →ₗ[B] M₂ i j)
    (hρr : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr i j))
    (hdiag : ∀ i, ρl i i = ρr i i)
    (M₃ : Fin k → Fin k → Fin k → Type u) [∀ i j l, AddCommGroup (M₃ i j l)] [∀ i j l, Module B (M₃ i j l)]
    (σ₁ : ∀ i j l, M₂ i j →ₗ[B] M₃ i j l) (σ₂ : ∀ i j l, M₂ i l →ₗ[B] M₃ i j l) (σ₃ : ∀ i j l, M₂ j l →ₗ[B] M₃ i j l)
    (hσ₃ : ∀ i j l, IsLocalizedModule (Submonoid.powers (f i)) (σ₃ i j l))
    (hcoc₁ : ∀ i j l, σ₁ i j l ∘ₗ ρl i j = σ₂ i j l ∘ₗ ρl i l)
    (hcoc₂ : ∀ i j l, σ₁ i j l ∘ₗ ρr i j = σ₃ i j l ∘ₗ ρl j l)
    (hcoc₃ : ∀ i j l, σ₂ i j l ∘ₗ ρr i l = σ₃ i j l ∘ₗ ρr j l) :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module B N) (π : ∀ i, N →ₗ[B] M i),
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i)) ∧
      (∀ i j, ρl i j ∘ₗ π i = ρr i j ∘ₗ π j) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalizedModule_exists_forall_isLocalizedModule_comp_eq_of_span_eq_top.solution
