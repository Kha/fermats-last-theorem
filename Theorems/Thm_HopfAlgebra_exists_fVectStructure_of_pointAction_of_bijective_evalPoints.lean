import Mathlib
import Definitions.Def_HopfAlgebra_FVectStructure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_fVectStructure_of_pointAction_of_bijective_evalPoints

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_fVectStructure_of_pointAction_of_bijective_evalPoints
    (K : Type u) [Field K] [PerfectField K]
    (H : Type v) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    [Finite (WithConv (H →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (H →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (H →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : H →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] H →ₐ[AlgebraicClosure K]
          (WithConv (H →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (F : Type) [Field F] [Fintype F]
    (smulF : F → WithConv (H →ₐ[K] AlgebraicClosure K) → WithConv (H →ₐ[K] AlgebraicClosure K))
    (h_one : ∀ x, smulF 1 x = x)
    (h_mul : ∀ (a b : F) x, smulF (a * b) x = smulF a (smulF b x))
    (h_zero : ∀ x, smulF 0 x = 1)
    (h_add : ∀ (a b : F) x, smulF (a + b) x = smulF a x * smulF b x)
    (h_pt_one : ∀ a : F, smulF a 1 = 1)
    (h_pt_mul : ∀ (a : F) x y, smulF a (x * y) = smulF a x * smulF a y)
    (h_gal : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F)
        (x y : WithConv (H →ₐ[K] AlgebraicClosure K)),
        (∀ h : H, WithConv.ofConv y h = σ (WithConv.ofConv x h)) →
        ∀ h : H, WithConv.ofConv (smulF a y) h = σ (WithConv.ofConv (smulF a x) h)) :
    ∃ σF : HopfAlgebra.FVectStructure F K H,
      ∀ (a : F) (x : WithConv (H →ₐ[K] AlgebraicClosure K)),
        WithConv.toConv ((WithConv.ofConv x).comp (σF.act a : H →ₐ[K] H)) = smulF a x := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_fVectStructure_of_pointAction_of_bijective_evalPoints.solution
