import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finite_of_normOneTorus_nTorsion_generators_and_points

open scoped TensorProduct in
theorem HopfAlgebra.finite_of_normOneTorus_nTorsion_generators_and_points
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (A : Type) [CommRing A] [HopfAlgebra K A] (u' v' : A)
    (hgen : Algebra.adjoin K {u', v'} = ⊤)
    (hrel : u' ^ 2 - algebraMap K A c * v' ^ 2 = 1)
    (hn : ∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1)
    (hlift : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      (w + z * δ) ^ n = 1 →
      ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) :
    Module.Finite K A := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finite_of_normOneTorus_nTorsion_generators_and_points.solution
