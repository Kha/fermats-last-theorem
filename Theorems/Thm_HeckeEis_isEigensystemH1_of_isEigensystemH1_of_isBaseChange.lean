import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange

set_option autoImplicit false

theorem HeckeEis.isEigensystemH1_of_isEigensystemH1_of_isBaseChange
    (N : ℕ) {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (S₀ : Set ℕ)
    {V₀ V : Type} [AddCommGroup V₀] [Module K₀ V₀] [AddCommGroup V] [Module K V]
    (ρ₀ : Representation K₀ (CongruenceSubgroup.Gamma0 N) V₀) (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (a₀ : ℕ → (V₀ →ₗ[K₀] V₀)) (a : ℕ → (V →ₗ[K] V))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (j : V₀ →ₛₗ[i] V) (hj : ∀ (g : CongruenceSubgroup.Gamma0 N) (v : V₀), j (ρ₀ g v) = ρ g (j v))
    (hja : ∀ (ℓ : ℕ) (v : V₀), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → j (a₀ ℓ v) = a ℓ (j v))
    (hbc : ∃ (ι : Type) (b₀ : Module.Basis ι K₀ V₀) (b : Module.Basis ι K V), ∀ s : ι, b s = j (b₀ s))
    (lam : ℕ → K₀) (h : HeckeEis.IsEigensystemH1 N ρ₀ a₀ S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ (fun ℓ => i (lam ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange.solution
