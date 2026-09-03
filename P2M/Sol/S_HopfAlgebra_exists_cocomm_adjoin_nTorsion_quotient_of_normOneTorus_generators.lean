import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_exists_cocomm_adjoin_normOneTorus_of_generators_and_points
import Theorems.Thm_HopfAlgebra_exists_cocomm_adjoin_nTorsion_quotient_of_adjoin_normOneTorus
import P2M.Util
namespace P2MW.S_HopfAlgebra_exists_cocomm_adjoin_nTorsion_quotient_of_normOneTorus_generators

open scoped TensorProduct

theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B : Type) [CommRing B] [HopfAlgebra K B] (u v : B)
    (hrel : u ^ 2 - algebraMap K B c * v ^ 2 = 1)
    (hcu : Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v))
    (hcv : Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u)
    (hliftB : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! f : B →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Coalgebra.IsCocomm K A ∧
      ∃ (u' v' : A),
        (Algebra.adjoin K {u', v'} = ⊤) ∧
        (u' ^ 2 - algebraMap K A c * v' ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u' = u' ⊗ₜ[K] u' + c • (v' ⊗ₜ[K] v')) ∧
        (Coalgebra.comul (R := K) v' = u' ⊗ₜ[K] v' + v' ⊗ₜ[K] u') ∧
        (∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          (w + z * δ) ^ n = 1 →
          ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) := by
  obtain ⟨B₀, iCR, iHA, hcc₀, u₀, v₀, hgen₀, hrel₀, hcu₀, hcv₀, hlift₀⟩ :=
    HopfAlgebra.exists_cocomm_adjoin_normOneTorus_of_generators_and_points
      K c hc hnsq B u v hrel hcu hcv hliftB
  letI := iCR; letI := iHA
  exact HopfAlgebra.exists_cocomm_adjoin_nTorsion_quotient_of_adjoin_normOneTorus
    K c hc hnsq n δ hδ B₀ hcc₀ u₀ v₀ hgen₀ hrel₀ hcu₀ hcv₀ hlift₀
