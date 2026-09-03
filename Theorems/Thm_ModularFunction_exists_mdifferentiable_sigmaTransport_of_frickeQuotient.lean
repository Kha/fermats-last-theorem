import Mathlib
import P2M.Util
import P2M.Sol.S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ))) :
    MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) ≠ 0 ∧
    ∃ G' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' ∧
      G' * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) =
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (P.map φ) ∧
      ∃ m : ℕ, ∀ M : ℕ, m ≤ M →
        (Function.Periodic ((G * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
          IsBoundedAtImInfty (G * ModularForm.discriminant ^ M) ∧
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
        (Function.Periodic ((G' * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
          IsBoundedAtImInfty (G' * ModularForm.discriminant ^ M) ∧
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G' * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
        ∀ (n : ℕ) (z : ↥K),
          (z : ℂ) = (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ M)).coeff n →
          (UpperHalfPlane.qExpansion N (G' * ModularForm.discriminant ^ M)).coeff n = φ z := by p2m_exact_reverting @_root_.P2MW.S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.solution
