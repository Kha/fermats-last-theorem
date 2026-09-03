import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.exists_subalgebra_eq_annihilator_vanishingIdealOfPoints
    (F : Type) [Field F] (A : Type) [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
    (L : Type) [Field L] [Algebra F L]
    (S : Submonoid (WithConv (A →ₐ[F] L)))
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) :
    ∃ B : Subalgebra F (CartierDual F A),
      (B : Set (CartierDual F A))
          = {θ | ∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S), θ a = 0} ∧
      (∀ θ ∈ B, Coalgebra.comul (R := F) θ
          ∈ Submodule.span F (Set.image2 (fun φ ψ => φ ⊗ₜ[F] ψ) (B : Set (CartierDual F A)) (B : Set (CartierDual F A)))) ∧
      (∀ θ ∈ B, HopfAlgebraStruct.antipode (R := F) (A := CartierDual F A) θ ∈ B) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints.solution
