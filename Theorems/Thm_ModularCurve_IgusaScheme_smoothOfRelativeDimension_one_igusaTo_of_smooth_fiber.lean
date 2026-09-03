import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_igusaTo_of_smooth_fiber

open CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_igusaTo_of_smooth_fiber
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    [Flat (igusaTo N ℓ)] [LocallyOfFinitePresentation (igusaTo N ℓ)]
    [IrreducibleSpace ↥(ModularCurve.IgusaScheme N ℓ)]
    (hfib : ∀ y : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)),
      Smooth ((igusaTo N ℓ).fiberToSpecResidueField y))
    (V : (ModularCurve.IgusaScheme N ℓ).Opens) (hV : (V : Set ↥(ModularCurve.IgusaScheme N ℓ)).Nonempty)
    [SmoothOfRelativeDimension 1 (V.ι ≫ igusaTo N ℓ)] :
    SmoothOfRelativeDimension 1 (igusaTo N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_igusaTo_of_smooth_fiber.solution
