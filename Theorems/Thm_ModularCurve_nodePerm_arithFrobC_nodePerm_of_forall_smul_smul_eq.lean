import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import P2M.Util
import P2M.Sol.S_ModularCurve_nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve ModularCurve

theorem ModularCurve.nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k]
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hfix : ∀ w ∈ W, arithFrobC q k N • (arithFrobC q k N • w) = w)
    (hstab : SemilinearAut.IsNodeStable (nodePairsOfPlaces (arithFrobC q k N) W)
      (arithFrobC q k N))
    (s : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) :
    SemilinearAut.nodePerm (nodePairsOfPlaces (arithFrobC q k N) W) (arithFrobC q k N) hstab
        (SemilinearAut.nodePerm (nodePairsOfPlaces (arithFrobC q k N) W) (arithFrobC q k N)
          hstab s) = s := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq.solution
