import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_CuspForm_AtkinLehnerOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_atkinLehnerLin_apply
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false
open CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.periodMap_atkinLehnerLin_apply {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (f : CuspForm (Gamma0 M) 2) (γ δ : Gamma0 M)
    (h : ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * W.mat
      = W.mat * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) :
    ModularCurve.periodMap M (CuspForm.atkinLehnerLin W 2 f) γ = ModularCurve.periodMap M f δ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_atkinLehnerLin_apply.solution
