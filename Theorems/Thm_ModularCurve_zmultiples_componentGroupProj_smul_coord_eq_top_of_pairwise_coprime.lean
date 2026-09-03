import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime

open ModularCurve

theorem ModularCurve.zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t))
    (s₀ : ι) :
    AddSubgroup.zmultiples (componentGroupProj e ((e s₀ : ℤ) •
      (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime.solution
