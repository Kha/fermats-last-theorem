import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul
attribute [-simp] Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk Rep.coe_tateδneg2_apply Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_dimShiftDownObjMap_apply

set_option autoImplicit false
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand ExtCitation

theorem Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul
    {H : Type} [Group H] [Fintype H] [DecidableEq H]
    (C : Rep ℤ H) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup H), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup H) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup H),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (p : ℕ) [Fact p.Prime]
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : H, C.ρ g d = d) ∧ (∑ g : H, C.ρ g c) = p • d)
    (B₀ : Rep ℤ H) [Fintype B₀] (hB₀ : ∀ b : B₀, p • b = 0) (htriv : ∀ (g : H) (b : B₀), B₀.ρ g b = b)
    (hX : (Rep.relationSeqInt B₀).ShortExact) (φ : Rep.relationModuleInt B₀ ⟶ C) :
    (∃ χ : Rep.free ℤ H B₀ ⟶ C, Rep.relationModuleInt.ι B₀ ≫ χ = φ) ∨
    (∃ y : groupCohomology B₀ 1,
      (groupCohomology.map (MonoidHom.id H) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul.solution
