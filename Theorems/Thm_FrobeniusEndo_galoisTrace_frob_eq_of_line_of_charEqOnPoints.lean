import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_FrobeniusEndo_galoisTrace_frob_eq_of_line_of_charEqOnPoints

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo
theorem FrobeniusEndo.galoisTrace_frob_eq_of_line_of_charEqOnPoints {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (p : ℕ) [Fact p.Prime] (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄k).Point p) = p ^ 2) (hpk : (p : k) ≠ 0) (a : ℤ) (hline : ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + Fintype.card F) (hpos : ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0) (hpt : FrobCharEqOnPoints W σ a (Fintype.card F)) : galoisTrace F W p σ = (Fintype.card F : ZMod p) + 1 - (Nat.card (W⁄F).Point : ZMod p) ∧ LinearMap.det (galoisRepModuleEnd F W p σ) = (Fintype.card F : ZMod p) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusEndo_galoisTrace_frob_eq_of_line_of_charEqOnPoints.solution
