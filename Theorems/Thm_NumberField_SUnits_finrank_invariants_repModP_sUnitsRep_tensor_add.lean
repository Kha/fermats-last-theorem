import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add
import Definitions.Def_Compat_Mathlib430
attribute [-instance] NumberField.LevelArith.instCommGroupUnitsModPow
attribute [-simp] NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module IsDedekindDomain NumberField NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.SUnits.finrank_invariants_repModP_sUnitsRep_tensor_add
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    {p : ℕ} [Fact p.Prime] (hG : (Nat.card (K ≃ₐ[E] K)).Coprime p)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))
    (M : Rep.{0} (ZMod p) (K ≃ₐ[E] K)) [FiniteDimensional (ZMod p) M] :
    Module.finrank (ZMod p) (repModP p (NumberField.SUnits.sUnitsRep E K S) ⊗ M : Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants +
      Module.finrank (ZMod p) M.ρ.invariants =
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) (K ≃ₐ[E] K)
          (Σ v : NumberField.InfinitePlace E, (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) ⊗ M :
          Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants +
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) (K ≃ₐ[E] K)
          (Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) ⊗ M :
          Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants +
      Module.finrank (ZMod p) (repTorsionP p (NumberField.SUnits.sUnitsRep E K S) ⊗ M : Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.solution
