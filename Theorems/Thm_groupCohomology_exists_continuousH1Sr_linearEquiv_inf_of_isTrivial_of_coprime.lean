import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_continuousH1Sr_linearEquiv_inf_of_isTrivial_of_coprime

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
p2m_open "CategoryTheory Module groupCohomology~exists_linearEquiv_H1_of_forall_iff_of_isUnit_index ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

theorem groupCohomology.exists_continuousH1Sr_linearEquiv_inf_of_isTrivial_of_coprime
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (M : Rep.{0} (ZMod p) ↥K.fixingSubgroup)
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → M.ρ s = 1)
    (V : Submodule (ZMod p) (H1 (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M)))
    (hV : ∀ x, x ∈ V ↔ ∃ c : cocycles₁ (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M), H1π _ c = x ∧
      ∀ g : ↥K.fixingSubgroup, ∃ a : M, ∀ s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup),
        (g⁻¹ * s * g : ↥K.fixingSubgroup) = t → M.ρ g (c t) - c s = M.ρ (s : ↥K.fixingSubgroup) a - a) :
    ∃ e : ↥(continuousH1Sr K.fixingSubgroup.subtype S M) ≃ₗ[ZMod p]
      ↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
          (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M) ⊓ V),
      ∀ y : ↥(continuousH1Sr K.fixingSubgroup.subtype S M),
        ((e y : ↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
            (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M) ⊓ V)) :
          H1 (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M)) =
        (H1InfRes M (L.fixingSubgroup.subgroupOf K.fixingSubgroup)).g.hom (y : H1 M) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_continuousH1Sr_linearEquiv_inf_of_isTrivial_of_coprime.solution
