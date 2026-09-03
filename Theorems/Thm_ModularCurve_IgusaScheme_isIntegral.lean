import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_isIntegral

open AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.isIntegral (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsIntegral (ModularCurve.IgusaScheme N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_isIntegral.solution
