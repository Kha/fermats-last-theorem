import Mathlib
import Definitions.Def_PDivisibleGroup_Dimension
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_formallyEtale_level_of_hasDimension_zero

set_option autoImplicit false

theorem PDivisibleGroup.formallyEtale_level_of_hasDimension_zero
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (hG : G.HasDimension 0) (v : ℕ) :
    Algebra.FormallyEtale R (G.level v) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_formallyEtale_level_of_hasDimension_zero.solution
