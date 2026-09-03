import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2
    (N : ℕ) [NeZero N] {κ : Type} [Field κ] (S₀ : Set ℕ)
    {V V'' : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] [AddCommGroup V''] [Module κ V'']
    (ρ : Representation κ (CongruenceSubgroup.Gamma0 N) V) (ρ'' : Representation κ (CongruenceSubgroup.Gamma0 N) V'')
    (a : ℕ → (V →ₗ[κ] V)) (a'' : ℕ → (V'' →ₗ[κ] V''))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (hcomm : ∀ ℓ ℓ' : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ℓ'.Prime → ¬ ℓ' ∣ N → ℓ' ∉ S₀ →
      a ℓ ∘ₗ a ℓ' = a ℓ' ∘ₗ a ℓ)
    (π : V →ₗ[κ] V'') (hπ : ∀ g : CongruenceSubgroup.Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)
    (hπa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → π ∘ₗ a ℓ = a'' ℓ ∘ₗ π)
    (hsurj : Function.Surjective π)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime) (hℓ₀N : ¬ ℓ₀ ∣ N) (hℓ₀S : ℓ₀ ∉ S₀)
    (hH2 : ∀ A : Rep κ ↥(CongruenceSubgroup.Gamma0 (N * ℓ₀)), Subsingleton (groupCohomology A 2))
    (lam : ℕ → κ) (hlam : lam ℓ₀ ≠ 0) (h : HeckeEis.IsEigensystemH1 N ρ'' a'' S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ lam := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2.solution
