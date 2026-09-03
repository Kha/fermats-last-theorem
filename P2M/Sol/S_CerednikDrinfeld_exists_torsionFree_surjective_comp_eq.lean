import Mathlib
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq

set_option autoImplicit false

theorem solution
    (p : ℕ) {S B : Type} [CommRing S] [CommRing B] (h : S →+* B) (hS : ∀ s : S, (p : S) * s = 0 → s = 0) :
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T) (q : T →+* B),
      (∀ t : T, (p : T) * t = 0 → t = 0) ∧ Function.Surjective q ∧ q.comp i = h := by
  classical
  refine ⟨MvPolynomial B S, inferInstance, MvPolynomial.C, MvPolynomial.eval₂Hom h id, ?_, ?_, ?_⟩
  · intro t ht
    have hC : (p : MvPolynomial B S) = MvPolynomial.C (p : S) := by simp
    rw [hC, MvPolynomial.C_mul'] at ht
    ext m
    have hm := congrArg (MvPolynomial.coeff m) ht
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero, smul_eq_mul] at hm
    rw [MvPolynomial.coeff_zero]
    exact hS _ hm
  · intro b
    exact ⟨MvPolynomial.X b, by simp⟩
  · ext s
    simp
