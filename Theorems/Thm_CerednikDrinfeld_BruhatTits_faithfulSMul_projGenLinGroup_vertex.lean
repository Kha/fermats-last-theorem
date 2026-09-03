import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Group.Action.Faithful
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex

set_option autoImplicit false

open CerednikDrinfeld.BruhatTits LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.faithfulSMul_projGenLinGroup_vertex
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    FaithfulSMul (Matrix.ProjGenLinGroup (Fin 2) K) (Vertex R K) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex.solution
