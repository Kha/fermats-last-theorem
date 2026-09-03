import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_exists_cocomm_normOneTorus_generators_and_points
import Theorems.Thm_HopfAlgebra_exists_finite_nTorsion_quotient_of_normOneTorus_generators
import P2M.Util
namespace P2MW.S_HopfAlgebra_exists_finite_cocomm_generated_normOneTorusNTorsion

open scoped TensorProduct

theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ (u v : A),
        (u ^ 2 - algebraMap K A c * v ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v)) ∧
        (Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u) ∧
        (∀ f : A →ₐ[K] AlgebraicClosure K, (f u + f v * δ) ^ n = 1) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          (w + z * δ) ^ n = 1 →
          ∃! f : A →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) := by
  obtain ⟨B, iCR, iHA, _hCC, u, v, hrel, hcu, hcv, hliftB⟩ :=
    HopfAlgebra.exists_cocomm_normOneTorus_generators_and_points K c hc hnsq n δ hδ
  letI := iCR; letI := iHA
  exact HopfAlgebra.exists_finite_nTorsion_quotient_of_normOneTorus_generators
    K c hc hnsq n δ hδ B u v hrel hcu hcv hliftB
