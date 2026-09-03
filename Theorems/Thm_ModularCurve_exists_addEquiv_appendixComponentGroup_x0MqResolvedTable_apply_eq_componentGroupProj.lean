import Mathlib
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_ComponentGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj

open ModularCurve MazurRapoportAppendix

theorem ModularCurve.exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) (he : ∀ x, 0 < e x) (s₀ : ι) :
    ∃ ψ : AppendixComponentGroup (x0MqResolvedTable e) ≃+ componentGroup e,
      (∀ (a : X0MqComponents e → ℤ) (ha : a ∈ degreeZeroSublattice (x0MqResolvedTable e)),
        ψ (appendixComponentGroupClass (x0MqResolvedTable e) ⟨a, ha⟩) =
          componentGroupProj e
            (((∑ s : ι, (∑ k : Fin (e s - 1), ((k : ℤ) + 1) * a (Sum.inr ⟨s, k⟩)) •
                  (LinearMap.proj s : (ι → ℤ) →ₗ[ℤ] ℤ)) +
                ((e s₀ : ℤ) * a (Sum.inl 1)) • (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ)).comp
              (characterLattice ι).subtype)) ∧
      ∃ hb : (Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inl 0) 1 : X0MqComponents e → ℤ) ∈
          degreeZeroSublattice (x0MqResolvedTable e),
        ψ (appendixComponentGroupClass (x0MqResolvedTable e) ⟨_, hb⟩) =
          componentGroupProj e ((e s₀ : ℤ) •
            (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj.solution
