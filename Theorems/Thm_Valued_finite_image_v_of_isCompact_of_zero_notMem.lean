import Mathlib
import P2M.Util
import P2M.Sol.S_Valued_finite_image_v_of_isCompact_of_zero_notMem

set_option autoImplicit false
open Topology in

theorem Valued.finite_image_v_of_isCompact_of_zero_notMem
    {R : Type*} [DivisionRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]
    (C : Set R) (hC : IsCompact C) (h0 : (0 : R) ∉ C) :
    ((fun x : R => Valued.v x) '' C).Finite := by p2m_exact_reverting @_root_.P2MW.S_Valued_finite_image_v_of_isCompact_of_zero_notMem.solution
