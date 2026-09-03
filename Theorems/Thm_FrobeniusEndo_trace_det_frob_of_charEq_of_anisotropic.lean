import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_FrobeniusEndo_trace_det_frob_of_charEq_of_anisotropic

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo
theorem FrobeniusEndo.trace_det_frob_of_charEq_of_anisotropic {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (a : ℤ) (q : ℕ) (hCE : galoisRepModuleEnd S W p σ * galoisRepModuleEnd S W p σ - (a : ZMod p) • galoisRepModuleEnd S W p σ + (q : ZMod p) • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p)) = 0) (hno : ¬ ∃ c : ZMod p, c ^ 2 - (a : ZMod p) * c + (q : ZMod p) = 0) : galoisTrace S W p σ = (a : ZMod p) ∧ LinearMap.det (galoisRepModuleEnd S W p σ) = (q : ZMod p) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusEndo_trace_det_frob_of_charEq_of_anisotropic.solution
