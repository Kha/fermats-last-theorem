import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_natCard_quot_range_verschiebung_sup_iSup_range_map_eq_natCard_primitives_quot_of_pow_eq_one
open scoped TensorProduct

theorem Deformation.DieudonneModule.natCard_quot_range_verschiebung_sup_iSup_range_map_eq_natCard_primitives_quot_of_pow_eq_one
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra (GaloisRep.ratLocalizedAt p) A]
    [Module.Finite (GaloisRep.ratLocalizedAt p) A] [Module.Flat (GaloisRep.ratLocalizedAt p) A]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) A]
    (hkill : ∀ f : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    {ι : Type} (ψ : ι → ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐc[ZMod p]
      (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)) :
    Nat.card (Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) ⧸
        ((Deformation.DieudonneModule.verschiebung (ZMod p) p
              ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)).range ⊔
          ⨆ i, (Deformation.DieudonneModule.map (ZMod p) p (ψ i)).range))
      = Nat.card (↥(primitives (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)) ⧸
          ⨆ i, ((primitives (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)).map
              (ψ i).toLinearMap).comap
            (primitives (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)).subtype) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_natCard_quot_range_verschiebung_sup_iSup_range_map_eq_natCard_primitives_quot_of_pow_eq_one.solution
