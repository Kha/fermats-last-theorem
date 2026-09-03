import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ThetaLevel_exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (ε : S) (hε : IsIdempotentElem ε)
    (w : Heis δ (N + 1) → Heis δ (N + 1))
    (hw : ∀ z : Heis δ (N + 1), ε • (T * schrodMat δ (N + 1) S (φB ω) e z) =
      ε • (schrodMat δ (N + 1) S (φB ω) e (w z) * T)) :
    ∃ γ : (Heis.Gam (δ := δ) (d := N + 1)),
      ∀ z : Heis δ (N + 1), ε • (T * schrodMat δ (N + 1) S (φB ω) e z) =
        ε • (schrodMat δ (N + 1) S (φB ω) e (γ.1 z) * T) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq.solution
