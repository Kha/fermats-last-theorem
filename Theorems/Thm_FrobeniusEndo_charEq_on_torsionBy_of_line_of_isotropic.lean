import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_FrobeniusEndo_charEq_on_torsionBy_of_line_of_isotropic

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo
theorem FrobeniusEndo.charEq_on_torsionBy_of_line_of_isotropic {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (hpK : (p : K) ≠ 0) (a : ℤ) (q : ℕ) (hline : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 → ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q) (hpos : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0) (hiso : ∃ c : ZMod p, c ^ 2 - (a : ZMod p) * c + (q : ZMod p) = 0) (P : (W⁄K).Point) (hP : (p : ℤ) • P = 0) : σ • (σ • P) - a • (σ • P) + (q : ℤ) • P = 0 := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusEndo_charEq_on_torsionBy_of_line_of_isotropic.solution
