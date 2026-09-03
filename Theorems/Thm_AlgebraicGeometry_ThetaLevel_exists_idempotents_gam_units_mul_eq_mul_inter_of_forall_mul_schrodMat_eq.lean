import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ThetaLevel_exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (hint : ∀ γ : (Heis.Gam (δ := δ) (d := N + 1)), ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, IsIntertwiner δ (N + 1) B ω e γ.1 U)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (hmono : ∀ z : Heis δ (N + 1), ∃ (ε : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)) → S) (u : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
        T * schrodMat δ (N + 1) S (φB ω) e z =
          (∑ c, ε c • ((u : S) • schrodMat δ (N + 1) S (φB ω) e ⟨0, c.1, c.2⟩)) * T) :
    ∃ (m : ℕ) (ε : Fin m → S) (γ : Fin m → (Heis.Gam (δ := δ) (d := N + 1))) (c : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
      ∀ k, ε k • T = ε k • ((c : S) • (ThetaLevel.inter δ (N + 1) B ω e ((γ k)⁻¹).1).map φB) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq.solution
