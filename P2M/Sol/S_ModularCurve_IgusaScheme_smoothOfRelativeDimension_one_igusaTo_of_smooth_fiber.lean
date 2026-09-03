import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import P2M.Util
namespace P2MW.S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_igusaTo_of_smooth_fiber

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    [Flat (igusaTo N ℓ)] [LocallyOfFinitePresentation (igusaTo N ℓ)]
    [IrreducibleSpace ↥(ModularCurve.IgusaScheme N ℓ)]
    (hfib : ∀ y : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)),
      Smooth ((igusaTo N ℓ).fiberToSpecResidueField y))
    (V : (ModularCurve.IgusaScheme N ℓ).Opens) (hV : (V : Set ↥(ModularCurve.IgusaScheme N ℓ)).Nonempty)
    [SmoothOfRelativeDimension 1 (V.ι ≫ igusaTo N ℓ)] :
    SmoothOfRelativeDimension 1 (igusaTo N ℓ) := by
  haveI : Smooth (igusaTo N ℓ) := Smooth.of_smooth_fiberToSpecResidueField _ hfib
  exact AlgebraicGeometry.smoothOfRelativeDimension_of_irreducibleSpace 1 (igusaTo N ℓ) V hV
