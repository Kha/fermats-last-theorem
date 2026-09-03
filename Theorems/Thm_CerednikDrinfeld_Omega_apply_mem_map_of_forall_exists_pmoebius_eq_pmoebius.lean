import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    (hunc : ¬ (Omega.upperHalfPlane K₀ K).Countable)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    (Δ : Subgroup G) (hcount : Countable ↥(Δ.map ρ))
    (g : G)
    (hg : ∀ z ∈ Omega.upperHalfPlane K₀ K, ∃ δ ∈ Δ, Omega.pmoebius K₀ (ρ g) z = Omega.pmoebius K₀ (ρ δ) z) :
    ρ g ∈ Δ.map ρ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius.solution
