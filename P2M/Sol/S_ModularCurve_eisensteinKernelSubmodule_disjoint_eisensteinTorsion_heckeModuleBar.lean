import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
namespace P2MW.S_ModularCurve_eisensteinKernelSubmodule_disjoint_eisensteinTorsion_heckeModuleBar
p2m_open "ModularCurve P2MW.S_ModularCurve_eisensteinKernelSubmodule_disjoint_eisensteinTorsion_heckeModuleBar.ModularCurve AlgebraicCurve"

namespace ModularCurve p2m_export "ModularCurve" "eisensteinKernelSubmodule HeckeAlg eisensteinKernel eisensteinIdeal JZero HeckeOperatorsCommuteBar heckeModuleBar" end ModularCurve
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.exists_one_add_smul_eq_zero_of_mem_eisensteinKernel_smul_top
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J] (I : Ideal HeckeAlg) {y : J}
    (hy : y ∈ eisensteinKernel J I • (⊤ : Submodule HeckeAlg J)) :
    ∃ i ∈ I, (1 + i) • y = 0 := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro t ht z _
    obtain ⟨i, hi, h⟩ := ht
    exact ⟨i, hi, by rw [← mul_smul]; exact h z⟩
  · rintro y₁ y₂ ⟨i₁, hi₁, h₁⟩ ⟨i₂, hi₂, h₂⟩
    refine ⟨i₁ + i₂ + i₁ * i₂, I.add_mem (I.add_mem hi₁ hi₂) (I.mul_mem_left i₁ hi₂), ?_⟩
    have e : (1 + (i₁ + i₂ + i₁ * i₂) : HeckeAlg) = (1 + i₁) * (1 + i₂) := by ring
    have t1 : ((1 + i₁) * (1 + i₂)) • y₁ = 0 := by rw [mul_comm, mul_smul, h₁, smul_zero]
    have t2 : ((1 + i₁) * (1 + i₂)) • y₂ = 0 := by rw [mul_smul, h₂, smul_zero]
    rw [smul_add, e, t1, t2, add_zero]

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.eq_zero_of_mem_eisensteinKernel_smul_top_of_torsion
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J] (I : Ideal HeckeAlg) {x : J}
    (hx : ∀ t ∈ I, t • x = 0)
    (hmem : x ∈ eisensteinKernel J I • (⊤ : Submodule HeckeAlg J)) : x = 0 := by
  obtain ⟨i, hi, h⟩ := exists_one_add_smul_eq_zero_of_mem_eisensteinKernel_smul_top I hmem
  rw [add_smul, one_smul, hx i hi, add_zero] at h
  exact h

theorem solution (p : ℕ)
    [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ x : JZero p, (∀ t ∈ eisensteinIdeal p, t • x = 0) →
      x ∈ eisensteinKernelSubmodule p (heckeModuleBar p) → x = 0 := by
  have _ := hcomm
  letI := heckeModuleBar p
  intro x hx hmem
  exact eq_zero_of_mem_eisensteinKernel_smul_top_of_torsion (eisensteinIdeal p) hx hmem
