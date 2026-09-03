import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_ringKrullDim_stalk_le_two

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.ringKrullDim_stalk_le_two (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (x : ↥(IgusaScheme N ℓ)) : ringKrullDim ((IgusaScheme N ℓ).presheaf.stalk x) ≤ 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_ringKrullDim_stalk_le_two.solution
