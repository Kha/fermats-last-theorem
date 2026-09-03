import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Theorems.Thm_AlgebraicCurve_ConstantReduction_placeMap_surjective
import P2M.Util
namespace P2MW.S_AlgebraicCurve_ConstantReduction_pic0Map_surjective

set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) [HasPrincipalDivisors L F] :
    Function.Surjective R.pic0Map := by
  classical
  intro z
  obtain ⟨Dbar, rfl⟩ := Pic0.mk_surjective z

  let s : Place (ResidueField A) Fbar → Place L F := Function.surjInv R.placeMap_surjective
  have hs : ∀ Q, R.placeMap (s Q) = Q := Function.surjInv_eq R.placeMap_surjective
  have hid : R.placeMap ∘ s = id := funext hs

  set D : Divisor L F := Finsupp.mapDomain s (Dbar : Divisor (ResidueField A) Fbar) with hDdef
  have hD : Finsupp.mapDomain R.placeMap D = (Dbar : Divisor (ResidueField A) Fbar) := by
    rw [hDdef, ← Finsupp.mapDomain_comp, hid, Finsupp.mapDomain_id]
  have hdeg : D ∈ Divisor.degZero (K := L) (F := F) := by
    rw [Divisor.mem_degZero, ← R.degree_mapDomain D, hD]
    exact Divisor.mem_degZero.mp Dbar.2
  refine ⟨Pic0.mk ⟨D, hdeg⟩, ?_⟩
  have hdz : R.degZeroMap ⟨D, hdeg⟩ = Dbar := by
    refine Subtype.ext ?_
    show (R.degZeroMap ⟨D, hdeg⟩ : Divisor (ResidueField A) Fbar) = (Dbar : Divisor (ResidueField A) Fbar)
    rw [R.coe_degZeroMap]
    exact hD
  rw [R.pic0Map_mk, hdz]
