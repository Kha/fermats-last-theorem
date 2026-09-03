import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal

set_option autoImplicit false

universe u

open IsLocalRing

theorem WeierstrassCurve.DrinfeldGlobal.originChart_rel_unique_of_mem_maximalIdeal
    {S : Type u} [CommRing S] [IsLocalRing S] (a₁ a₂ a₃ a₄ a₆ x v v' : S)
    (hx : x ∈ maximalIdeal S) (hv : v ∈ maximalIdeal S) (hv' : v' ∈ maximalIdeal S)
    (h : v + a₁ * x * v + a₃ * v ^ 2 = x ^ 3 + a₂ * x ^ 2 * v + a₄ * x * v ^ 2 + a₆ * v ^ 3)
    (h' : v' + a₁ * x * v' + a₃ * v' ^ 2 = x ^ 3 + a₂ * x ^ 2 * v' + a₄ * x * v' ^ 2 + a₆ * v' ^ 3) :
    v = v' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_originChart_rel_unique_of_mem_maximalIdeal.solution
