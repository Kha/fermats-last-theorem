import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (t : Γ(Y, ⊤)) (ht : t ≠ 0) (η : Y)
    (hηt : η ∉ Y.basicOpen t) (hmax : ∀ y : Y, y ⤳ η → y ∉ Y.basicOpen t → y = η) :
    ringKrullDim (Y.presheaf.stalk η) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen.solution
