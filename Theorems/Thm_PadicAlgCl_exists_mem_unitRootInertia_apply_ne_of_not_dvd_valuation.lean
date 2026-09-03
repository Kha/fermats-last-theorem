import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation
attribute [-instance] ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete
attribute [-simp] ExtCitation.LocalLevel.coe_smul_OO

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem PadicAlgCl.exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : ¬ (p : ℤ) ∣ Padic.valuation x)
    (γ : PadicAlgCl p) (hγ : γ ^ p = algebraMap ℚ_[p] (PadicAlgCl p) x) :
    ∃ τ ∈ ResidualGaloisRep.unitRootInertia p, ResidualGaloisRep.localAut p τ γ ≠ γ := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation.solution
