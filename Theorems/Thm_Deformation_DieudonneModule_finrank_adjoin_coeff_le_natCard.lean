import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_finrank_adjoin_coeff_le_natCard

universe u v

theorem Deformation.DieudonneModule.finrank_adjoin_coeff_le_natCard
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (C : Type v) [CommRing C] [Bialgebra k C]
    (N : AddSubgroup (Deformation.DieudonneModule k p C)) [Finite N]
    (hF : ∀ z ∈ N, Deformation.DieudonneModule.frobenius k p C z ∈ N)
    (hV : ∀ z ∈ N, Deformation.DieudonneModule.verschiebung k p C z ∈ N) :
    Module.Finite k ↥(Algebra.adjoin k {c : C | ∃ (n : ℕ) (x : Deformation.wittHom k p n C) (i : Fin n),
        Deformation.DieudonneModule.of k p C n x ∈ N ∧ (x : TruncatedWittVector p n C).coeff i = c}) ∧
      Module.finrank k ↥(Algebra.adjoin k {c : C | ∃ (n : ℕ) (x : Deformation.wittHom k p n C) (i : Fin n),
        Deformation.DieudonneModule.of k p C n x ∈ N ∧ (x : TruncatedWittVector p n C).coeff i = c}) ≤
      Nat.card N := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_finrank_adjoin_coeff_le_natCard.solution
