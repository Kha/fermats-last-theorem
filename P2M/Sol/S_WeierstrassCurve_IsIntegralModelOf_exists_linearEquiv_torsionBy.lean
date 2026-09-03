import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_WeierstrassCurve_exists_linearEquiv_torsionBy_of_variableChange_eq
import P2M.Util
namespace P2MW.S_WeierstrassCurve_IsIntegralModelOf_exists_linearEquiv_torsionBy

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ} (h : W.IsIntegralModelOf E) (n : ℕ) : ∃ φ : Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point n), φ (σ • x) = σ • φ x := by
  obtain ⟨C, hC⟩ := h
  exact WeierstrassCurve.exists_linearEquiv_torsionBy_of_variableChange_eq (AlgebraicClosure ℚ) C hC n
