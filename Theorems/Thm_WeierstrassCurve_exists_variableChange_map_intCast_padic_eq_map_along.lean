import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_map_intCast_padic_eq_map_along

open scoped WeierstrassCurve.Affine in
theorem WeierstrassCurve.exists_variableChange_map_intCast_padic_eq_map_along
    (R : Type) [CommRing R] [IsDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) (W₀ : WeierstrassCurve R) (heq : W₀⁄ℚ = E)
    {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (f : R →+* ℤ_[p])
    (hfc : ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r)) :
    ∃ C : WeierstrassCurve.VariableChange ℚ_[p],
      C • ((W₀.map f)⁄ℚ_[p]) = W.map (Int.castRingHom ℚ_[p]) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_map_intCast_padic_eq_map_along.solution
