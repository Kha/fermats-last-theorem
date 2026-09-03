import Mathlib
import Definitions.Def_ModularCurve_MazurPrincipleCore
import P2M.Util
import P2M.Sol.S_RibetLevelLowering_natCard_quotient_eq_natCard_quotient_of_eisenstein_ker_of_eisenstein_coker

set_option autoImplicit false
open ModularCurve

theorem RibetLevelLowering.natCard_quotient_eq_natCard_quotient_of_eisenstein_ker_of_eisenstein_coker
    {X : Type*} [AddCommGroup X] [Module HeckeAlg X]
    {Ψ : Type*} [AddCommGroup Ψ] [Module HeckeAlg Ψ]
    (θ : X →ₗ[HeckeAlg] Ψ) (η : HeckeAlg) (S : Finset Nat.Primes)
    (hker : ∀ x : X, θ x = 0 → ∀ ℓ : Nat.Primes, ℓ ∉ S →
      ∃ y : X, (heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • x = η • y)
    (hcoker : ∀ (ψ : Ψ) (ℓ : Nat.Primes), ℓ ∉ S →
      ∃ x : X, (heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1)) • ψ = θ x)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (heis : ¬ IsEventuallyEisenstein 𝔪) (hη : η ∈ 𝔪) :
    Nat.card (X ⧸ (𝔪 • (⊤ : Submodule HeckeAlg X))) =
      Nat.card (Ψ ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Ψ))) := by p2m_exact_reverting @_root_.P2MW.S_RibetLevelLowering_natCard_quotient_eq_natCard_quotient_of_eisenstein_ker_of_eisenstein_coker.solution
