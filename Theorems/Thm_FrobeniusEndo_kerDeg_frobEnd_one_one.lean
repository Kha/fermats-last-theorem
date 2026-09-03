import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.FieldTheory.Finite.Basic
import P2M.Util
import P2M.Sol.S_FrobeniusEndo_kerDeg_frobEnd_one_one

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo
theorem FrobeniusEndo.kerDeg_frobEnd_one_one {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) : kerDeg (frobEnd W σ) 1 1 = Nat.card (W⁄F).Point := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusEndo_kerDeg_frobEnd_one_one.solution
