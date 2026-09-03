import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_bijective_evalPoints_hopfKer_of_bijective_evalPoints

open scoped TensorProduct

universe u v

theorem HopfAlgebra.bijective_evalPoints_hopfKer_of_bijective_evalPoints
    (K : Type u) [Field K]
    (A : Type v) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Finite (WithConv (A →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
          (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (W : Submonoid (WithConv (A →ₐ[K] AlgebraicClosure K)))
    (Ā : Type v) [CommRing Ā] [HopfAlgebra K Ā] (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (hker₁ : ∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K,
        ∃ ν : WithConv (A →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = h)
    (hker₂ : ∀ ν ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃ w ∈ W, ν' = ν * w)
    (hrank : Module.finrank K ↥(HopfAlgebra.hopfKer π) * Nat.card ↥W = Module.finrank K A) :
    ∃ (_ : Finite (WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K))),
      Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] ↥(HopfAlgebra.hopfKer π) →ₐ[AlgebraicClosure K]
          (WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_bijective_evalPoints_hopfKer_of_bijective_evalPoints.solution
