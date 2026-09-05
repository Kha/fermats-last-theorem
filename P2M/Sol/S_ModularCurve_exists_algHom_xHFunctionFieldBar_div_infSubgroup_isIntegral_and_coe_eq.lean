import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL

import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_finiteAlong_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import P2M.Util
namespace P2MW.S_ModularCurve_exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

namespace AlphaCoeH

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem T_mem_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  apply Gamma1_le_GammaH
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]

end AlphaCoeH

open AlphaCoeH in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)] :
    ∃ (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)),
      αH.toRingHom.IsIntegral ∧
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex := finiteIndex_GammaH M H
  haveI : (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)).FiniteIndex := finiteIndex_GammaH (M / p) (infSubgroup p M H hpM)
  have hTM : ModularGroup.T ∈ CohCarrier.GammaH M H := T_mem_GammaH M H
  have hTN : ModularGroup.T ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := T_mem_GammaH (M / p) (infSubgroup p M H hpM)
  have hle : CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) :=
    ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM
  have hFle : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ xHFunctionFieldBar M H :=
    IntermediateField.adjoin.mono (AlgebraicClosure ℚ) _ _ (Set.image_mono (qExpFunctionFieldC_mono ℚ hle))
  let αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H) :=
    IntermediateField.inclusion hFle
  have hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun u => IntermediateField.coe_inclusion hFle u
  have hfinα : FiniteAlong (AlgebraicClosure ℚ) αH :=
    ModularCurve.finiteAlong_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) hTN hTM αH
  have hαint : αH.toRingHom.IsIntegral := by
    letI := algebraAlong αH
    haveI : Module.Finite ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := hfinα
    intro x
    exact Algebra.IsIntegral.isIntegral (R := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) x
  exact ⟨αH, hαint, hαq⟩

