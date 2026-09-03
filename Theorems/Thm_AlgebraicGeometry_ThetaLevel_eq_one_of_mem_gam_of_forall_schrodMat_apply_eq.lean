import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ThetaLevel_eq_one_of_mem_gam_of_forall_schrodMat_apply_eq

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.eq_one_of_mem_gam_of_forall_schrodMat_apply_eq
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] [Nontrivial B] (ζ ω : B) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d) (h : ∀ z : Heis δ d, schrodMat δ d B ω e (γ z) = schrodMat δ d B ω e z) :
    γ = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_eq_one_of_mem_gam_of_forall_schrodMat_apply_eq.solution
