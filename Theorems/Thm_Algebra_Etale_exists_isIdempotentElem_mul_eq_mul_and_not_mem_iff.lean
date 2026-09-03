import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff
    {S B C : Type} [CommRing S] [CommRing B] [CommRing C] [Algebra S B] [Algebra S C] [Algebra.Etale S B]
    (x y : B →ₐ[S] C) :
    ∃ e : C, IsIdempotentElem e ∧ (∀ b : B, e * x b = e * y b) ∧
      (algebraMap C (Localization.Away e)).comp x.toRingHom = (algebraMap C (Localization.Away e)).comp y.toRingHom ∧
      (∀ 𝔭 : Ideal C, 𝔭.IsPrime → (e ∉ 𝔭 ↔ ∀ b : B, x b - y b ∈ 𝔭)) ∧
      (∀ (k : Type) [Field k] (χ : C →+* k), χ.comp x.toRingHom = χ.comp y.toRingHom → χ e = 1) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff.solution
