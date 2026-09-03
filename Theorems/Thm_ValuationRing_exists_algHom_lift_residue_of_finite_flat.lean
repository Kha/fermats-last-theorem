import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationRing_exists_algHom_lift_residue_of_finite_flat

theorem ValuationRing.exists_algHom_lift_residue_of_finite_flat
    {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K]
    {H : Type*} [CommRing H] [Algebra R H] [Module.Finite R H] [Module.Flat R H]
    (φ : H →ₐ[R] IsLocalRing.ResidueField R) :
    ∃ ψ : H →ₐ[R] R, ∀ h, IsLocalRing.residue R (ψ h) = φ h := by p2m_exact_reverting @_root_.P2MW.S_ValuationRing_exists_algHom_lift_residue_of_finite_flat.solution
