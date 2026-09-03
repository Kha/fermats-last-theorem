import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_bijective_cartierModule_of_map_nsmul_eq
attribute [-instance] MvFormalGroup.CartierModule.instModuleWittVector MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u v

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_bijective_cartierModule_of_map_nsmul_eq
    (p : ℕ) [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (L : Type u) [Field L] [CharP L p] [PerfectRing L p]
    (t t' : Rigidified p Φ L)
    (Ψ : MvFormalGroup 2 L) [Ψ.IsComm] (ρL : Ψ.Hom t.X.F) (ρL' : Ψ.Hom t'.X.F)
    (hρL : Series.map (Ideal.Quotient.mk (pIdeal p L)) ρL.toPowerSeries = t.ρ)
    (hρL' : Series.map (Ideal.Quotient.mk (pIdeal p L)) ρL'.toPowerSeries = t'.ρ)
    (θ : MvFormalGroup.CartierModule p t.X.F →+ MvFormalGroup.CartierModule p t'.X.F)
    (hθ : Function.Bijective θ)
    (hθF : ∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
      MvFormalGroup.CartierModule.frobenius (θ f))
    (hθV : ∀ f, θ (MvFormalGroup.CartierModule.verschiebung f) =
      MvFormalGroup.CartierModule.verschiebung (θ f))
    (hθh : ∀ (a : L) f, θ (MvFormalGroup.CartierModule.homothety a f) =
      MvFormalGroup.CartierModule.homothety a (θ f))
    (hθa : ∀ (a : Zp2 p) f, θ (MvFormalGroup.CartierModule.endAct (t.X.actEnd a) f) =
      MvFormalGroup.CartierModule.endAct (t'.X.actEnd a) (θ f))
    (hθϖ : ∀ f, θ (MvFormalGroup.CartierModule.endAct t.X.varpiEnd f) =
      MvFormalGroup.CartierModule.endAct t'.X.varpiEnd (θ f))
    (hθρ : ∃ c : ℕ, ∀ f : MvFormalGroup.CartierModule p Ψ,
      θ (MvFormalGroup.CartierModule.map ρL (p ^ (c + t'.n) • f)) =
        MvFormalGroup.CartierModule.map ρL' (p ^ (c + t.n) • f)) :
    t.IsIsomorphic t' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_bijective_cartierModule_of_map_nsmul_eq.solution
