import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_SchematicClosure
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable
    (O : Type) [CommRing O] (F : Type) [Field F] [Algebra O F]
    (A : Type) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
    [Coalgebra.IsCocomm O A]
    (L : Type) [Field L] [Algebra F L]
    (S : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L)))
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) :
    ((HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S) :
        Set (TensorProduct O F (CartierDual O A)))
        = {w | ∀ x ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S),
            CartierDual.dualBaseChangeLin O F A w x = 0}) ∧
    IsComulStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) ∧
    IsAntipodeStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable.solution
