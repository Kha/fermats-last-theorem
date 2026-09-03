import Mathlib
import P2M.Util
import P2M.Sol.S_exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top

set_option autoImplicit false

theorem exteriorPower.range_map_subtype_eq_maximalIdeal_smul_top {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {d : ℕ} (hd : Module.finrank R M = d)
    (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (R ⧸ IsLocalRing.maximalIdeal R)) :
    LinearMap.range (exteriorPower.map d N.subtype) = IsLocalRing.maximalIdeal R • ⊤ := by p2m_exact_reverting @_root_.P2MW.S_exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top.solution
