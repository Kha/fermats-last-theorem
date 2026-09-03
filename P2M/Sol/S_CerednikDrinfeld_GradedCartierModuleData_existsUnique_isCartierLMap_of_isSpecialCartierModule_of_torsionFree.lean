import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_frobenius_mem_range_lambda_of_isSpecialCartierModule
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_existsUnique_isCartierLMap_of_isSpecialCartierModule_of_torsionFree

set_option autoImplicit false

p2m_open "CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData"

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule) :
    ∃! L : D.M →+ D.NMod, D.IsCartierLMap L := by
  classical
  obtain ⟨γ, hγ⟩ := hD.1
  have hinj : Function.Injective D.lambda :=
    lambda_injective_of_isHomogeneousVBasis_of_torsionFree p j hB D γ hγ
  have hmem : ∀ x : D.M, D.frobenius x ∈ LinearMap.range D.lambda :=
    frobenius_mem_range_lambda_of_isSpecialCartierModule p j D hD
  choose pre hpre using fun x => LinearMap.mem_range.1 (hmem x)
  let L : D.M →+ D.NMod :=
    { toFun := pre
      map_zero' := hinj (by rw [hpre, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [hpre, map_add, map_add, hpre, hpre]) }
  have hL : ∀ x, D.lambda (L x) = D.frobenius x := hpre
  refine ⟨L, ⟨?_, ?_, hL⟩, ?_⟩
  · intro w x
    apply hinj
    rw [hL, D.frobenius_smul, LinearMap.map_smul, hL]
  · intro x
    apply hinj
    rw [hL, lambda_nMk, map_zero, add_zero, D.frobenius_verschiebung, D.varpi_varpi]
  · intro L' hL'
    ext x
    apply hinj
    rw [hL'.lambda_comp, hL]
