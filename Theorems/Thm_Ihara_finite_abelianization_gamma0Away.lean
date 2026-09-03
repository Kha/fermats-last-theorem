import Definitions.Def_Gamma0Away
import Mathlib.GroupTheory.Abelianization.Defs
import P2M.Util
import P2M.Sol.S_Ihara_finite_abelianization_gamma0Away
attribute [-instance] Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway
attribute [-simp] Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply

set_option autoImplicit false

theorem Ihara.finite_abelianization_gamma0Away {N q : ℕ} (hq : q.Prime) (hqN : N.Coprime q) :
    Finite (Abelianization ↥(Ihara.Gamma0Away N q)) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_finite_abelianization_gamma0Away.solution
