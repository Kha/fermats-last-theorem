import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun (N ℓ : ℕ) [NeZero ℓ]
    {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : V →ₗ[K] V)
    (ha : ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
      a ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a) :
    ∃ T : HeckeEis.coeffH1par ρ →ₗ[K] HeckeEis.coeffH1par ρ,
      ∀ z : ↥(HeckeEis.coeffParabolicCocycles ρ), ∃ w : ↥(HeckeEis.coeffParabolicCocycles ρ),
        (w : CongruenceSubgroup.Gamma0 N → V) = HeckeEis.coeffHeckeFun N ℓ ρ a z ∧
          T (HeckeEis.coeffH1parMk ρ z) = HeckeEis.coeffH1parMk ρ w := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun.solution
