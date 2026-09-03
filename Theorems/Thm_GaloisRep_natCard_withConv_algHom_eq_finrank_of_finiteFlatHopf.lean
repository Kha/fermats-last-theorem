import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf
import P2M.Util
import P2M.Sol.S_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
open GaloisRep
theorem GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
    (q : ℕ) [Fact q.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H] :
    Nat.card (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
      = Module.finrank (GaloisRep.ratLocalizedAt q) H := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf.solution
