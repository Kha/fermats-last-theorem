import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy

theorem Submodule.natCard_torsionBySet_pow_linear_of_finite_torsionBy
    (T : Type*) [CommRing T] (G : Type*) [AddCommGroup G] [Module T G]
    (q : ℕ) [Fact q.Prime] (hfin : Finite ↥(Submodule.torsionBy ℤ G (q : ℤ)))
    (I : Ideal T) (hqI : (q : T) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) * q ^ C := by p2m_exact_reverting @_root_.P2MW.S_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy.solution
