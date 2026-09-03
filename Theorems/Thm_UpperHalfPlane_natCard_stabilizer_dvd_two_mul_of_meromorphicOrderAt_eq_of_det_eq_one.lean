import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one
    (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (F : ℍ → ℂ) (τ : ℍ)
    (hF : ∀ γ ∈ Γ, γ • τ = τ → ∀ᶠ z in 𝓝[≠] τ, F (γ • z) = F z)
    (n : ℤ) (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one.solution
