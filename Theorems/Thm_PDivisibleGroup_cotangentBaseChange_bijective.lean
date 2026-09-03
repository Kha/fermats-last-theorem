import Mathlib
import Definitions.Def_PDivisibleGroup_BaseChange
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_cotangentBaseChange_bijective

set_option autoImplicit false

theorem PDivisibleGroup.cotangentBaseChange_bijective
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [CommRing S] [Algebra R S] [Nontrivial S] (v : ℕ) :
    Function.Bijective (G.cotangentBaseChange S v) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_cotangentBaseChange_bijective.solution
