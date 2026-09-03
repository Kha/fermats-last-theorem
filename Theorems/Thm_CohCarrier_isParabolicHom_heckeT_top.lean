import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_isParabolicHom_heckeT_top
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false

theorem CohCarrier.isParabolicHom_heckeT_top (N ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N ⊤ A) (hφ : ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N ⊤) φ) :
    ModularCurve.Period.IsParabolicHom (CohCarrier.GammaH N ⊤) (CohCarrier.heckeT N ⊤ ℓ A φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_isParabolicHom_heckeT_top.solution
