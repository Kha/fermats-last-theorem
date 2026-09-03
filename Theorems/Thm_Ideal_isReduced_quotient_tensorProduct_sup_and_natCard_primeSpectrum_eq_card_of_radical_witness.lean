import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness

set_option autoImplicit false

open Polynomial TensorProduct

universe u v

theorem Ideal.isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
    (𝔭inf 𝔭zero : Ideal A) [𝔭inf.IsPrime] [𝔭zero.IsPrime]
    (hpinf : (p : A) ∈ 𝔭inf)
    (hcover : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → (p : A) ∈ 𝔮 → 𝔭inf ≤ 𝔮 ∨ 𝔭zero ≤ 𝔮)
    (j jp u v : A) (huv : u * v = (p : A) ^ 12) (huzero : u ∈ 𝔭zero) (huinf : u ∉ 𝔭inf)
    (κ : Type v) [Field κ] [CharP κ p]
    (θ : A ⊗[ℤ] κ →+* κ[X]) (hθs : Function.Surjective θ)
    (hθk : RingHom.ker θ =
      𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))
    (hθj : θ (j ⊗ₜ 1) = X) (hθjp : θ (jp ⊗ₜ 1) = X ^ p)
    (hrel : j - jp ^ p ∈ 𝔭zero)
    (S : Finset κ) (n : κ → ℕ) (hn : ∀ a ∈ S, 0 < n a) (c : κ) (hc : c ≠ 0)
    (hθu : θ (u ⊗ₜ 1) = C c * ∏ a ∈ S, (X - C a) ^ n a) :
    IsReduced ((A ⊗[ℤ] κ) ⧸
        (𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ⊔
         𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))) ∧
    Nat.card (PrimeSpectrum ((A ⊗[ℤ] κ) ⧸
        (𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ⊔
         𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))))
      = S.card := by p2m_exact_reverting @_root_.P2MW.S_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness.solution
