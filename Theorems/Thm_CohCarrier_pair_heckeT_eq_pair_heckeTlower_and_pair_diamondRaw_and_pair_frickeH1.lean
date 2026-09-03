import Mathlib
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Fricke
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_CupPairing
import P2M.Util
import P2M.Sol.S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false

theorem CohCarrier.pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (φ ψ : CohCarrier.H1 N H ℚ)
    (hφ : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N H) φ)
    (hψ : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N H) ψ) :
    (∀ (q : ℕ) [NeZero q],
      ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) (CohCarrier.heckeT N H q ℚ φ) ψ =
        ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) φ (CohCarrier.heckeTlower N H q ℚ ψ)) ∧
    (∀ σ : CongruenceSubgroup.Gamma0 N,
      ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) (CohCarrier.diamondRaw N H ℚ σ φ)
          (CohCarrier.diamondRaw N H ℚ σ ψ) =
        ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) φ ψ) ∧
    ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) (CohCarrier.frickeH1 N H ℚ φ)
        (CohCarrier.frickeH1 N H ℚ ψ) =
      ModularCurve.CupPairing.pair (CohCarrier.GammaH N H) φ ψ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_pair_heckeT_eq_pair_heckeTlower_and_pair_diamondRaw_and_pair_frickeH1.solution
