import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_IharaIota
import P2M.Util
import P2M.Sol.S_HeckeEis_mem_coeffCoboundaries_of_forall_apply_infty_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_coeffCoboundaries_of_forall_apply_infty_eq_zero (N p : ℕ) [NeZero p] (hpN : Nat.Coprime p N)
    (K : Type*) [CommRing K]
    {z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K}
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hz0 : ∀ γ : CongruenceSubgroup.Gamma0 (N * p),
      z (Ihara.ι₀ N p γ) (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧ : ModularCurve.ProjectiveLine (ZMod p)) = 0) :
    z ∈ HeckeEis.coeffCoboundaries ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_mem_coeffCoboundaries_of_forall_apply_infty_eq_zero.solution
