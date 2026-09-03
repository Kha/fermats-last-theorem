import Mathlib
import Definitions.Def_Patching_CohenMacaulayOfDim
import P2M.Util
import P2M.Sol.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {d : ℕ}
    (h : IsCohenMacaulayOfDim R d) (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) + p.height = d := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.solution
