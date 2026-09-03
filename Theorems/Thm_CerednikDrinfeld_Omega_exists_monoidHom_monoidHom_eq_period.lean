import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_eq_period

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega hiding exists_monoidHom_isAutomorphicWithMultiplier_theta period_symm

theorem CerednikDrinfeld.Omega.exists_monoidHom_monoidHom_eq_period
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a z₀ w : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hw : w ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (haz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ a)
    (hwa : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ w) (hwz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ w)
    (hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ u ∈ upperHalfPlane K₀ K,
      ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ x y u z) :
    ∃ Q : G →* G →* Kˣ, ∀ α β : G, ((Q α β : Kˣ) : K) = period ρ a z₀ α β := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_monoidHom_monoidHom_eq_period.solution
