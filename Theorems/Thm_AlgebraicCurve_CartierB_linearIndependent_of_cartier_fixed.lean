import Definitions.Def_AlgebraicCurve_IsCurveOver
import Mathlib.FieldTheory.Perfect
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CartierB_linearIndependent_of_cartier_fixed

theorem AlgebraicCurve.CartierB.linearIndependent_of_cartier_fixed {K F : Type*} [Field K]
    [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K] (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (η : Ω[F⁄K]), C (f ^ p • η) = f • C η)
    {n : ℕ} {w : Fin n → Ω[F⁄K]} (hfix : ∀ i, C (w i) = w i)
    (hFp : ∀ c : Fin n → ℕ, ∑ i, c i • w i = 0 → ∀ i, p ∣ c i) :
    LinearIndependent K w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CartierB_linearIndependent_of_cartier_fixed.solution
