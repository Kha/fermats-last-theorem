import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsLocalRing_map_ringEquiv_mem_principalUnits_iff

set_option autoImplicit false
open IsLocalRing
theorem IsLocalRing.map_ringEquiv_mem_principalUnits_iff {R : Type*} [CommRing R] [IsLocalRing R]
    (σ : R ≃+* R) {k : ℕ} {u : Rˣ} :
    Units.map (σ : R →* R) u ∈ principalUnits R k ↔ u ∈ principalUnits R k := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_map_ringEquiv_mem_principalUnits_iff.solution
