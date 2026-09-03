import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (ζ ω : B) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (T : Matrix (Fin n) (Fin n) B) (hT : ∀ z : Heis δ d, T * schrodMat δ d B ω e z = schrodMat δ d B ω e z * T) :
    ∃ c : B, T = c • (1 : Matrix (Fin n) (Fin n) B) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul.solution
