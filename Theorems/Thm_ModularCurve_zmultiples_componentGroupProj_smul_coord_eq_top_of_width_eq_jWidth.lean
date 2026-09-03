import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_JWidth
import P2M.Util
import P2M.Sol.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_width_eq_jWidth

open ModularCurve

theorem ModularCurve.zmultiples_componentGroupProj_smul_coord_eq_top_of_width_eq_jWidth
    {K : Type*} [Field K] [DecidableEq K] {ι : Type*} [Fintype ι] (e : ι → ℕ)
    (j : ι → K) (hj : Function.Injective j) (he : ∀ s, e s = jWidth (j s)) (s₀ : ι) :
    AddSubgroup.zmultiples (componentGroupProj e ((e s₀ : ℤ) •
      (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_width_eq_jWidth.solution
