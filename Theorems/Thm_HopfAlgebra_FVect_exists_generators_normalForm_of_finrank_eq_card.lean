import Definitions.Def_HopfAlgebra_FVectStructure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import P2M.Util
import P2M.Sol.S_HopfAlgebra_FVect_exists_generators_normalForm_of_finrank_eq_card

universe u v

theorem HopfAlgebra.FVect.exists_generators_normalForm_of_finrank_eq_card
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [CharZero R']
    (p r : ℕ) [Fact p.Prime] [NeZero r]
    (F : Type*) [Field F] [Fintype F] (hF : Fintype.card F = p ^ r)
    (hq : IsUnit ((p ^ r : R') - 1))
    (χ : Fˣ →* R'ˣ) (ι : F →+* IsLocalRing.ResidueField R')
    (hχ : ∀ l : Fˣ, IsLocalRing.residue R' (χ l : R') = ι l)
    (B : Type v) [CommRing B] [HopfAlgebra R' B] [Module.Finite R' B] [Module.Free R' B]
    (hrank : Module.finrank R' B = p ^ r)
    (fv : HopfAlgebra.FVectStructure F R' B) :
    ∃ (X : Fin r → B) (δ : Fin r → R'),
      (∀ i (l : Fˣ), (fv.act l) (X i) = (((χ ^ p ^ (i : ℕ)) l : R'ˣ) : R') • X i) ∧
      (∀ i, X i ^ p = δ i • X (i + 1)) ∧
      (∀ i, δ i ∣ (p : R')) ∧
      (∀ i, Coalgebra.counit (R := R') (X i) = 0) ∧
      Algebra.adjoin R' (Set.range X) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_FVect_exists_generators_normalForm_of_finrank_eq_card.solution
