import Definitions.Def_ModularCurve_IgusaScheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_isProper_igusaTo

open AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.isProper_igusaTo (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)] :
    IsProper (igusaTo N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_isProper_igusaTo.solution
