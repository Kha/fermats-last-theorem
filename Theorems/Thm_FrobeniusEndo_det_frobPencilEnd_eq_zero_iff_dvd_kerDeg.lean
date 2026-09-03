import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_FrobeniusEndo_det_frobPencilEnd_eq_zero_iff_dvd_kerDeg

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo
theorem FrobeniusEndo.det_frobPencilEnd_eq_zero_iff_dvd_kerDeg {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] (hfin : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) ≠ 0) {m n : ℤ} (hpos : kerDeg (frobEnd W σ) m n ≠ 0) : LinearMap.det (frobPencilEnd W σ p m n) = 0 ↔ p ∣ kerDeg (frobEnd W σ) m n := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusEndo_det_frobPencilEnd_eq_zero_iff_dvd_kerDeg.solution
