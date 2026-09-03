import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective
attribute [-instance] Rep.relationCarrier.instAddCommGroup
attribute [-simp] Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk Rep.coe_tateδneg2_apply Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_dimShiftDownObjMap_apply

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective
    {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (p : ℕ) [Fact p.Prime]
    {SB : ShortComplex (Rep ℤ G)} (hSB : SB.ShortExact) [Fintype SB.X₁] [Fintype SB.X₃]
    (hB₁ : ∀ b : SB.X₃, p • b = 0)
    (N : Subgroup G) (hpN : p ∣ Nat.card ↥N) (hN : ∀ g ∈ N, ∀ b : SB.X₃, SB.X₃.ρ g b = b)

    {R_B P_B : Rep ℤ G} (f_B : R_B ⟶ P_B) (g_B : P_B ⟶ SB.X₁) (w_B : f_B ≫ g_B = 0)
    (hT_B : (ShortComplex.mk f_B g_B w_B).ShortExact)
    (hP_B : ∀ (X Y : Rep ℤ G) (e : X ⟶ Y), Function.Surjective e.hom → ∀ χ : P_B ⟶ Y, ∃ χ' : P_B ⟶ X, χ' ≫ e = χ)
    {R_I P_I : Rep ℤ G} (f_I : R_I ⟶ P_I) (g_I : P_I ⟶ SB.X₂) (w_I : f_I ≫ g_I = 0)
    (hT_I : (ShortComplex.mk f_I g_I w_I).ShortExact)
    (hP_I : ∀ (X Y : Rep ℤ G) (e : X ⟶ Y), Function.Surjective e.hom → ∀ χ : P_I ⟶ Y, ∃ χ' : P_I ⟶ X, χ' ≫ e = χ)

    (ιR : R_B ⟶ R_I) (ιP : P_B ⟶ P_I) (sq₁ : f_B ≫ ιP = ιR ≫ f_I) (sq₂ : g_B ≫ SB.f = ιP ≫ g_I)
    (φ : R_B ⟶ C)
    (hφ : ∀ y : groupCohomology SB.X₁ 1,
      (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hT_B 1 2 rfl).hom y) = 0) :
    ∃ (ψ : R_I ⟶ C) (χ : P_B ⟶ C), φ = ιR ≫ ψ + f_B ≫ χ := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective.solution
