import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
namespace P2MW.S_WeierstrassCurve_exists_variableChange_map_intCast_padic_eq_map_along

set_option maxHeartbeats 3200000

open scoped WeierstrassCurve.Affine in
theorem solution
    (R : Type) [CommRing R] [IsDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) (W₀ : WeierstrassCurve R) (heq : W₀⁄ℚ = E)
    {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (f : R →+* ℤ_[p])
    (hfc : ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r)) :
    ∃ C : WeierstrassCurve.VariableChange ℚ_[p],
      C • ((W₀.map f)⁄ℚ_[p]) = W.map (Int.castRingHom ℚ_[p]) := by
  obtain ⟨C₀, hC₀⟩ := hW
  refine ⟨C₀.map (algebraMap ℚ ℚ_[p]), ?_⟩
  have hcomp : (algebraMap ℤ_[p] ℚ_[p]).comp f = (algebraMap ℚ ℚ_[p]).comp (algebraMap R ℚ) := by
    ext r; simpa using hfc r
  have h1 : (W₀.map f)⁄ℚ_[p] = E.map (algebraMap ℚ ℚ_[p]) := by
    show (W₀.map f).map (algebraMap ℤ_[p] ℚ_[p]) = E.map (algebraMap ℚ ℚ_[p])
    rw [WeierstrassCurve.map_map, hcomp, ← WeierstrassCurve.map_map, ← heq]
    rfl
  have h2 : W.map (Int.castRingHom ℚ_[p]) =
      (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) := by
    rw [WeierstrassCurve.map_map]; rfl
  rw [h1, h2, ← hC₀]
  exact WeierstrassCurve.map_variableChange (C := C₀) (W := E) (φ := algebraMap ℚ ℚ_[p])
