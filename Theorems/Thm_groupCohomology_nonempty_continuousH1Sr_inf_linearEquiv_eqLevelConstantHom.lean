import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_GroupCohomology_LevelConstantHom
import P2M.Util
import P2M.Sol.S_groupCohomology_nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem groupCohomology.nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (M : Rep.{0} (ZMod p) ↥K.fixingSubgroup)
    (hM : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → M.ρ s = 1)
    (V : Submodule (ZMod p) (H1 (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M)))
    (hV : ∀ x, x ∈ V ↔ ∃ c : cocycles₁ (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M), H1π _ c = x ∧
      ∀ g : ↥K.fixingSubgroup, ∃ a : M, ∀ s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup),
        (g⁻¹ * s * g : ↥K.fixingSubgroup) = t → M.ρ g (c t) - c s = M.ρ (s : ↥K.fixingSubgroup) a - a) :
    Nonempty (↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
        (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M) ⊓ V) ≃ₗ[ZMod p]
      ↥(eqLevelConstantHom K.fixingSubgroup.subtype S (L.fixingSubgroup.subgroupOf K.fixingSubgroup) M)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom.solution
