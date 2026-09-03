import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo
theorem FrobeniusEndo.dvd_kerDeg_of_det_frobPencilEnd_eq_zero {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] {m n : ℤ} (h : LinearMap.det (frobPencilEnd W σ p m n) = 0) : p ∣ kerDeg (frobEnd W σ) m n := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero.solution
