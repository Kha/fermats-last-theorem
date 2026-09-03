import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import P2M.Util
import P2M.Sol.S_FinFlatHopf_not_isLocalRing_dual_of_isLocalRing

theorem FinFlatHopf.not_isLocalRing_dual_of_isLocalRing
    (B : Type) [CommRing B] [IsLocalRing B] (n : ℕ) (hn1 : 1 < n)
    (hn : (n : B) ∉ IsLocalRing.maximalIdeal B ^ 2)
    (H : Type) [CommRing H] [HopfAlgebra B H] [Module.Free B H] [Module.Finite B H]
    (hrank : Module.finrank B H = n) [IsLocalRing H] :
    ¬ IsLocalRing (WithConv (H →ₗ[B] B)) := by p2m_exact_reverting @_root_.P2MW.S_FinFlatHopf_not_isLocalRing_dual_of_isLocalRing.solution
