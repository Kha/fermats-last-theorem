import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_cocycles1_conj_apply_sub_eq

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.cocycles1_conj_apply_sub_eq
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (c : cocycles₁ A) (g s : G) :
    A.ρ g (c (g⁻¹ * s * g)) - c s = A.ρ s (c g) - c g := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_cocycles1_conj_apply_sub_eq.solution
