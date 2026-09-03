import Mathlib
import P2M.Util
import P2M.Sol.S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul

set_option autoImplicit false

universe u

open scoped TensorProduct Polynomial

theorem Module.free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (a : A) (m n : ℕ) (hn : 1 ≤ n)
    (hfin : (Polynomial.aeval a : R[X] →ₐ[R] A).toRingHom.Finite)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) = m)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) = n * m := by p2m_exact_reverting @_root_.P2MW.S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul.solution
