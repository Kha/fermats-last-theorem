import Mathlib
import P2M.Util
namespace P2MW.S_IsIntegral_of_forall_isPrime_isIntegral_quotient_mk

set_option autoImplicit false

universe u v

open Polynomial

theorem solution
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] (a : A)
    (h : ∀ (p : Ideal A), p.IsPrime → IsIntegral R (Ideal.Quotient.mk p a)) :
    IsIntegral R a := by
  classical

  let T : Submonoid A :=
    { carrier := {x | ∃ p : Polynomial R, p.Monic ∧ Polynomial.aeval a p = x}
      one_mem' := ⟨1, Polynomial.monic_one, by simp⟩
      mul_mem' := by
        rintro x y ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
        exact ⟨p * q, hp.mul hq, by simp⟩ }
  by_contra hnot

  have hdisj : Disjoint ((nilradical A : Ideal A) : Set A) (T : Set A) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, mem_nilradical] at hx
    obtain ⟨n, hn⟩ := hx
    apply hnot
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    ·
      rw [h0, pow_zero] at hn
      haveI : Subsingleton A := subsingleton_of_zero_eq_one hn.symm
      exact ⟨Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
    · refine ⟨p ^ n, hp.pow n, ?_⟩
      rw [← Polynomial.aeval_def, map_pow, hn]
  obtain ⟨P, hP, -, hPT⟩ := Ideal.exists_le_prime_disjoint (nilradical A) T hdisj
  obtain ⟨q, hq, hq0⟩ := h P hP
  have hmem : Polynomial.aeval a q ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Polynomial.aeval (Ideal.Quotient.mk P a) q = Ideal.Quotient.mkₐ R P (Polynomial.aeval a q) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    rw [← Polynomial.aeval_def] at hq0
    rw [← Ideal.Quotient.mkₐ_eq_mk R, ← this, hq0]
  exact Set.disjoint_left.mp hPT hmem ⟨q, hq, rfl⟩
