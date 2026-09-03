import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Prod
import P2M.Util
import P2M.Sol.S_IharaLemma_resInj_of_reduction

set_option autoImplicit false

theorem IharaLemma.resInj_of_reduction {R : Type*} [CommRing R] {V L Vk Lk : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup L] [Module R L]
    [AddCommGroup Vk] [Module R Vk] [AddCommGroup Lk] [Module R Lk]
    (ϖ : R) (f : V →ₗ[R] L) (redV : V →ₗ[R] Vk) (redL : L →ₗ[R] Lk)
    (fk : Vk →ₗ[R] Lk) (hsq : ∀ v, redL (f v) = fk (redV v))
    (hker : ∀ v, redV v = 0 → ∃ v₁, v = ϖ • v₁) (hϖ : ∀ x : L, redL (ϖ • x) = 0)
    (hfk : Function.Injective fk) :
    ∀ (v : V) (x : L), f v = ϖ • x → ∃ v₁ : V, v = ϖ • v₁ := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_resInj_of_reduction.solution
