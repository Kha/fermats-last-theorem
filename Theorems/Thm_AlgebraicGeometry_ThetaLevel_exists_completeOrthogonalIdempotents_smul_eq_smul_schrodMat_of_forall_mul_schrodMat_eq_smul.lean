import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul

set_option autoImplicit false

open scoped BigOperators
p2m_open "AlgebraicGeometry AlgebraicGeometry.ThetaLevel~exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul"

theorem AlgebraicGeometry.ThetaLevel.exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (T : Matrix (Fin n) (Fin n) B) (hT : IsUnit T) (lam mu : HH δ → B)
    (hθ : ∀ h' : HH δ, T * schrodMat δ d B ω e (Heis.theta h') = lam h' • (schrodMat δ d B ω e (Heis.theta h') * T))
    (hη : ∀ k' : HH δ, T * schrodMat δ d B ω e (Heis.eta k') = mu k' • (schrodMat δ d B ω e (Heis.eta k') * T)) :
    ∃ (ε : HH δ × HH δ → B) (u : Bˣ), CompleteOrthogonalIdempotents ε ∧
      ∀ c : HH δ × HH δ, ε c • T = (ε c * u) • schrodMat δ d B ω e ⟨0, c.1, c.2⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_exists_completeOrthogonalIdempotents_smul_eq_smul_schrodMat_of_forall_mul_schrodMat_eq_smul.solution
