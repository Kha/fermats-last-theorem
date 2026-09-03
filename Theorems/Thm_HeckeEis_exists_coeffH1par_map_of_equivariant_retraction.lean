import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_map_of_equivariant_retraction
    (N : ℕ) (K : Type*) [CommRing K]
    {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (ρ' : Representation K (CongruenceSubgroup.Gamma0 N) V')
    (i : V →ₗ[K] V') (r : V' →ₗ[K] V)
    (hi : ∀ g : CongruenceSubgroup.Gamma0 N, i ∘ₗ ρ g = ρ' g ∘ₗ i)
    (hr : ∀ g : CongruenceSubgroup.Gamma0 N, r ∘ₗ ρ' g = ρ g ∘ₗ r)
    (hri : r ∘ₗ i = LinearMap.id) :
    ∃ (I : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ')
      (R : HeckeEis.coeffH1par ρ' →ₗ[K] HeckeEis.coeffH1par ρ),
      R ∘ₗ I = LinearMap.id ∧
      (∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ),
        ∃ z' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
          (z' : CongruenceSubgroup.Gamma0 N → V') = i ∘ (z : CongruenceSubgroup.Gamma0 N → V) ∧
          I (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ' z') ∧
      (∀ z' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
        ∃ z : ↥(HeckeEis.coeffParabolicCocycles ρ),
          (z : CongruenceSubgroup.Gamma0 N → V) = r ∘ (z' : CongruenceSubgroup.Gamma0 N → V') ∧
          R (HeckeEis.coeffH1parMk ρ' z') = HeckeEis.coeffH1parMk ρ z) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (a : V →ₗ[K] V) (a' : V' →ₗ[K] V'), i ∘ₗ a = a' ∘ₗ i →
        ∀ (T : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ)
          (T' : HeckeEis.coeffH1par ρ' →ₗ[K] HeckeEis.coeffH1par ρ'),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ρ),
              (w : CongruenceSubgroup.Gamma0 N → V) = HeckeEis.coeffHeckeFun N ℓ ρ a z ∧
              T (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ w) →
          (∀ z' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
            ∃ w' : ↥(HeckeEis.coeffParabolicCocycles ρ'),
              (w' : CongruenceSubgroup.Gamma0 N → V') = HeckeEis.coeffHeckeFun N ℓ ρ' a' z' ∧
              T' (HeckeEis.coeffH1parMk ρ' z') = HeckeEis.coeffH1parMk ρ' w') →
          T' ∘ₗ I = I ∘ₗ T) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction.solution
