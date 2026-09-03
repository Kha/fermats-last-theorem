import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Prod
import P2M.Util
namespace P2MW.S_IharaLemma_square_localized

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] (S : Submonoid R) {V Vk V' Vk' L L' Lk Lk' : Type*}
    [AddCommGroup V] [Module R V] [AddCommGroup Vk] [Module R Vk]
    [AddCommGroup V'] [Module R V'] [AddCommGroup Vk'] [Module R Vk']
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    [AddCommGroup Lk] [Module R Lk] [AddCommGroup Lk'] [Module R Lk']
    (f : V →ₗ[R] L) (redV : V →ₗ[R] Vk) (redL : L →ₗ[R] Lk) (fk : Vk →ₗ[R] Lk)
    (hsq : ∀ v, redL (f v) = fk (redV v))
    (gV : V →ₗ[R] V') [IsLocalizedModule S gV] (gK : Vk →ₗ[R] Vk') [IsLocalizedModule S gK]
    (gL : L →ₗ[R] L') (gLk : Lk →ₗ[R] Lk') [IsLocalizedModule S gLk]
    (f' : V' →ₗ[R] L') (hf' : ∀ v, f' (gV v) = gL (f v))
    (redV' : V' →ₗ[R] Vk') (hredV' : ∀ v, redV' (gV v) = gK (redV v))
    (redL' : L' →ₗ[R] Lk') (hredL' : ∀ x, redL' (gL x) = gLk (redL x))
    (fk' : Vk' →ₗ[R] Lk') (hfk' : ∀ y, fk' (gK y) = gLk (fk y)) :
    ∀ v', redL' (f' v') = fk' (redV' v') := by
  have h : redL' ∘ₗ f' = fk' ∘ₗ redV' := by
    apply IsLocalizedModule.linearMap_ext S gV gLk
    ext v
    simp only [LinearMap.comp_apply, hf', hredL', hsq, ← hfk', hredV']
  intro v'
  exact LinearMap.congr_fun h v'
