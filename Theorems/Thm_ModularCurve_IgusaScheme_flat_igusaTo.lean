import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_flat_igusaTo

open AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.flat_igusaTo (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Flat (igusaTo N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_flat_igusaTo.solution
