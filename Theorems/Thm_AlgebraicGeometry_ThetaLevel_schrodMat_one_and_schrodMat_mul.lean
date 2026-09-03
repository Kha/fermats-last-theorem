import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.schrodMat_one_and_schrodMat_mul
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B) (hω : ω ^ (2 * d) = 1)
    {n : ℕ} (e : Fin n ≃ HH δ) :
    schrodMat δ d B ω e 1 = 1 ∧
      ∀ z z' : Heis δ d, schrodMat δ d B ω e (z * z') = schrodMat δ d B ω e z * schrodMat δ d B ω e z' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul.solution
