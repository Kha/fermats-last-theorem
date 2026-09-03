import Mathlib
import P2M.Util
import P2M.Sol.S_DoubleCoset_natCard_quotient_eq_natCard_quotient_map_of_surjective

set_option autoImplicit false

open scoped MatrixGroups

theorem DoubleCoset.natCard_quotient_eq_natCard_quotient_map_of_surjective
    {G Q : Type*} [Group G] [Group Q] (f : G →* Q) (hf : Function.Surjective f)
    (H K : Subgroup G) (hH : f.ker ≤ H) :
    Nat.card (DoubleCoset.Quotient (H : Set G) (K : Set G)) =
      Nat.card (DoubleCoset.Quotient (H.map f : Set Q) (K.map f : Set Q)) := by p2m_exact_reverting @_root_.P2MW.S_DoubleCoset_natCard_quotient_eq_natCard_quotient_map_of_surjective.solution
