import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_IharaIota
import P2M.Util
import P2M.Sol.S_HeckeEis_coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom (N p : ℕ) [NeZero p]
    (hpN : Nat.Coprime p N) (K : Type*) [CommRing K] (ℓ : ℕ) [NeZero ℓ] (hℓ : Nat.Coprime ℓ (N * p))
    {z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K}
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (φ : Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)
    (hφ : ∀ γ : CongruenceSubgroup.Gamma0 (N * p),
      φ (Additive.ofMul γ) = z (Ihara.ι₀ N p γ) (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧ : ModularCurve.ProjectiveLine (ZMod p)))
    (γ : CongruenceSubgroup.Gamma0 (N * p)) :
    HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.projLineAlphaAdj p K ℓ) z (Ihara.ι₀ N p γ) (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧ : ModularCurve.ProjectiveLine (ZMod p))
      = HeckeEis.heckeOperatorHom (N * p) ℓ K φ (Additive.ofMul γ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom.solution
