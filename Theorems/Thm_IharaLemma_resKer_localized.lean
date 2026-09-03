import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Prod
import P2M.Util
import P2M.Sol.S_IharaLemma_resKer_localized

set_option autoImplicit false

theorem IharaLemma.resKer_localized {R : Type*} [CommRing R] (S : Submonoid R) {V Vk V' Vk' : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup Vk] [Module R Vk]
    [AddCommGroup V'] [Module R V'] [AddCommGroup Vk'] [Module R Vk']
    (ϖ : R) (redV : V →ₗ[R] Vk)
    (hker : ∀ v, redV v = 0 → ∃ v₁, v = ϖ • v₁)
    (gV : V →ₗ[R] V') [IsLocalizedModule S gV] (gK : Vk →ₗ[R] Vk') [IsLocalizedModule S gK]
    (red' : V' →ₗ[R] Vk') (hsq : ∀ v, red' (gV v) = gK (redV v)) :
    ∀ v' : V', red' v' = 0 → ∃ v₁' : V', v' = ϖ • v₁' := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_resKer_localized.solution
