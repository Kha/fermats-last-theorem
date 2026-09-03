import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ThetaLevel_exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq

set_option autoImplicit false

open scoped BigOperators
p2m_open "AlgebraicGeometry AlgebraicGeometry.ThetaLevel~exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul"

theorem AlgebraicGeometry.ThetaLevel.exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (hint : ∀ γ : (Heis.Gam (δ := δ) (d := N + 1)), ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, IsIntertwiner δ (N + 1) B ω e γ.1 U)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (ε : S) (hε : IsIdempotentElem ε)
    (γ : (Heis.Gam (δ := δ) (d := N + 1)))
    (hγ : ∀ z : Heis δ (N + 1), ε • (T * schrodMat δ (N + 1) S (φB ω) e z) =
      ε • (schrodMat δ (N + 1) S (φB ω) e (γ.1 z) * T)) :
    ∃ c : Sˣ, ε • T = ε • ((c : S) • (ThetaLevel.inter δ (N + 1) B ω e γ.1).map φB) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_exists_units_smul_eq_smul_map_inter_of_forall_smul_mul_schrodMat_eq.solution
