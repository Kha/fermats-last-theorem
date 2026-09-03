import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom
    (N : ℕ) {R : Type} [CommRing R] {κ : Type} [CommRing κ] (f : R →+* κ)
    {Λ : Type} [AddCommGroup Λ] [Module R Λ] {Λ' : Type} [AddCommGroup Λ'] [Module κ Λ']
    (ρR : Representation R (Gamma0 N) Λ) (ρ' : Representation κ (Gamma0 N) Λ')
    (red : Λ →+ Λ') (hreds : ∀ (c : R) (x : Λ), red (c • x) = f c • red x)
    (hredρ : ∀ (g : Gamma0 N) (x : Λ), red (ρR g x) = ρ' g (red x))
    (a : ℕ → (Λ →ₗ[R] Λ)) (a' : ℕ → (Λ' →ₗ[κ] Λ')) (hreda : ∀ (ℓ : ℕ) (x : Λ), red (a ℓ x) = a' ℓ (red x)) :
    ∃ Φ : HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρ',
      (∀ z : ↥(HeckeEis.coeffCocycles ρR), ∃ w : ↥(HeckeEis.coeffCocycles ρ'),
        (∀ g : Gamma0 N, (w : Gamma0 N → Λ') g = red ((z : Gamma0 N → Λ) g)) ∧
          Φ (HeckeEis.coeffH1Mk ρR z) = HeckeEis.coeffH1Mk ρ' w) ∧
      (∀ (c : R) (x : HeckeEis.coeffH1 ρR), Φ (c • x) = f c • Φ x) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (T : HeckeEis.coeffH1 ρR →ₗ[R] HeckeEis.coeffH1 ρR)
          (T' : HeckeEis.coeffH1 ρ' →ₗ[κ] HeckeEis.coeffH1 ρ'),
        HeckeEis.IsCoeffHeckeOnH1 N ℓ ρR (a ℓ) T → HeckeEis.IsCoeffHeckeOnH1 N ℓ ρ' (a' ℓ) T' →
          ∀ x : HeckeEis.coeffH1 ρR, Φ (T x) = T' (Φ x)) ∧
      ∀ ϖ : R, Function.Surjective red → (∀ x : Λ, red x = 0 ↔ ∃ y : Λ, x = ϖ • y) → (∀ x : Λ, ϖ • x = 0 → x = 0) →
        ∀ x : HeckeEis.coeffH1 ρR, Φ x = 0 ↔ ∃ y : HeckeEis.coeffH1 ρR, x = ϖ • y := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom.solution
