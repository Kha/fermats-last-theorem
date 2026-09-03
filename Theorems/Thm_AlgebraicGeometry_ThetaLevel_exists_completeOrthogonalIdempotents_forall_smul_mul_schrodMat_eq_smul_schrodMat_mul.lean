import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul

set_option autoImplicit false

open scoped BigOperators
p2m_open "AlgebraicGeometry AlgebraicGeometry.ThetaLevel~schrodMat_one_and_schrodMat_mul"

theorem AlgebraicGeometry.ThetaLevel.exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (hmono : ∀ z : Heis δ (N + 1), ∃ (ε : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)) → S) (u : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
        T * schrodMat δ (N + 1) S (φB ω) e z =
          (∑ c, ε c • ((u : S) • schrodMat δ (N + 1) S (φB ω) e ⟨0, c.1, c.2⟩)) * T) :
    ∃ (m : ℕ) (ε : Fin m → S) (w : Fin m → Heis δ (N + 1) → Heis δ (N + 1)),
      CompleteOrthogonalIdempotents ε ∧
      ∀ (p : Fin m) (z : Heis δ (N + 1)),
        ε p • (T * schrodMat δ (N + 1) S (φB ω) e z) = ε p • (schrodMat δ (N + 1) S (φB ω) e (w p z) * T) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_forall_smul_mul_schrodMat_eq_smul_schrodMat_mul.solution
