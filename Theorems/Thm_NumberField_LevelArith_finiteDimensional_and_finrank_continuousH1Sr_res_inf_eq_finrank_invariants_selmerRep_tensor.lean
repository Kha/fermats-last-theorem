import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.LevelArith.finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup → N.ρ s = 1)
    (V : Submodule (ZMod p) (H1 (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype
      (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)))))
    (hV : ∀ x, x ∈ V ↔ ∃ c : cocycles₁ (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype
        (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))), H1π _ c = x ∧
      ∀ g : ↥K.fixingSubgroup, ∃ a : N.twist ((cycloChar p).comp K.fixingSubgroup.subtype),
        ∀ s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup), (g⁻¹ * s * g : ↥K.fixingSubgroup) = t →
          (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)).ρ g (c t) - c s =
            (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)).ρ (s : ↥K.fixingSubgroup) a - a) :
    FiniteDimensional (ZMod p)
        ↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
            (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ⊓ V) ∧
      Module.finrank (ZMod p)
          ↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
              (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ⊓ V) =
        Module.finrank (ZMod p) (selmerRep K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor.solution
