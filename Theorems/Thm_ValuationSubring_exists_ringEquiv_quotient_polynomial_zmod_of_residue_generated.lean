import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated

set_option autoImplicit false

universe u

open Polynomial
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ValuationSubring.exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated
    {F : Type u} [Field F] (W : ValuationSubring F) (p : ℕ) [Fact p.Prime]
    (hp0 : ((p : ℕ) : F) ≠ 0) (hpW : ((p : ℕ) : F) ∈ W.nonunits)
    (A : Subalgebra ℤ F) (hAW : ∀ a : F, a ∈ A → a ∈ W)
    (s : F) (hs : s ∈ A) (hint : ∀ a : F, a ∈ A → IsIntegral ↥(Algebra.adjoin ℤ ({s} : Set F)) a)
    (hgen : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.aeval s P ∈ W ∧ (Polynomial.aeval s P)⁻¹ ∈ W)
    (t : F) (ht : t ∈ A)
    (hres : ∀ x : F, x ∈ W → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      x * Polynomial.aeval t Q - Polynomial.aeval t P ∈ W.nonunits)
    (P₀ : Polynomial ℤ) (hsP₀ : s - Polynomial.aeval t P₀ ∈ W.nonunits)
    (𝔭 : Ideal ↥A) (h𝔭 : ∀ a : ↥A, a ∈ 𝔭 ↔ (a : F) ∈ W.nonunits) :
    ∃ e : (↥A ⧸ 𝔭) ≃+* Polynomial (ZMod p),
      ∀ (a : ↥A) (P : Polynomial ℤ), ((a : F) - Polynomial.aeval t P) ∈ W.nonunits →
        e (Ideal.Quotient.mk 𝔭 a) = P.map (Int.castRingHom (ZMod p)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated.solution
