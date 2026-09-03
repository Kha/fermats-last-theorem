import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_constant_and_rootsOfUnity_models_of_rank

theorem HopfAlgebra.exists_constant_and_rootsOfUnity_models_of_rank
    (R : Type) [CommRing R] [Nontrivial R] (q : ℕ) [NeZero q]
    (L : Type) [Field L] [CharZero L] [IsAlgClosed L] [Algebra R L] :
    (∃ (K : Type) (_ : CommRing K) (_ : HopfAlgebra R K),
        Module.Finite R K ∧ Module.Flat R K ∧ Module.finrank R K = q ∧
        Nat.card (K →ₐ[R] L) = q ∧ Nonempty (K ≃ₐ[R] (Fin q → R))) ∧
    (∃ (K : Type) (_ : CommRing K) (_ : HopfAlgebra R K),
        Module.Finite R K ∧ Module.Flat R K ∧ Module.finrank R K = q ∧
        Nat.card (K →ₐ[R] L) = q ∧
        Nonempty (K ≃ₐ[R]
          (Polynomial R ⧸ Ideal.span {(Polynomial.X : Polynomial R) ^ q - 1}))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_constant_and_rootsOfUnity_models_of_rank.solution
