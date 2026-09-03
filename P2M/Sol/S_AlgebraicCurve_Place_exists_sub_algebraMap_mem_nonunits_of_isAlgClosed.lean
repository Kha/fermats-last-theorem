import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

theorem solution
    {κ' : Type*} [Field κ'] [IsAlgClosed κ'] {F' : Type*} [Field F'] [Algebra κ' F']
    (P' : Place κ' F') [P'.FiniteResidue]
    (x : F') (hx : x ∈ P'.toValuationSubring) :
    ∃ c : κ', x - algebraMap κ' F' c ∈ P'.toValuationSubring.nonunits := by
  classical
  haveI : Module.Finite κ' P'.ResidueField := AlgebraicCurve.Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral κ' P'.ResidueField := Algebra.IsIntegral.of_finite κ' _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ') (K := P'.ResidueField)).2
    (IsLocalRing.residue _ ⟨x, hx⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨x, hx⟩ : P'.toValuationSubring) - algebraMap κ' P'.toValuationSubring c ∈
      IsLocalRing.maximalIdeal P'.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc,
      IsScalarTower.algebraMap_apply κ' P'.toValuationSubring P'.ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
      sub_self]
  have e : ((⟨x, hx⟩ - algebraMap κ' P'.toValuationSubring c : P'.toValuationSubring) : F') = x - algebraMap κ' F' c := by
    change P'.toValuationSubring.subtype (⟨x, hx⟩ - algebraMap κ' P'.toValuationSubring c) = _
    rw [map_sub]
    rfl
  rw [← e]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr hmem
