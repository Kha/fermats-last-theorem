import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_smul_eq_map_short_of_isUnit_two_three

set_option autoImplicit false

universe u

theorem WeierstrassCurve.exists_variableChange_smul_eq_map_short_of_isUnit_two_three
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (h2 : IsUnit ((2 : ℕ) : R₀)) (h3 : IsUnit ((3 : ℕ) : R₀)) (W : WeierstrassCurve K) :
    ∃ (C : WeierstrassCurve.VariableChange K) (a b : R₀),
      C • W = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_map_short_of_isUnit_two_three.solution
