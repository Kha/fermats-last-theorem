import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_GroupCohomology_LevelConstantHom
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L) :
    ∃ e : (selmerRep K L hKL S p) ≃ₗ[ZMod p]
        ↥(levelConstantHom (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S (ZMod p) (ZMod p)),
      ∀ (g : ↥K.fixingSubgroup) (x : selmerRep K L hKL S p) (s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)),
        (g⁻¹ * s * g : ↥K.fixingSubgroup) = t →
          (e ((selmerRep K L hKL S p).ρ g x) : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) s =
            ((((cycloChar p).comp K.fixingSubgroup.subtype) g : (ZMod p)ˣ) : ZMod p) *
              (e x : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) t := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom.solution
