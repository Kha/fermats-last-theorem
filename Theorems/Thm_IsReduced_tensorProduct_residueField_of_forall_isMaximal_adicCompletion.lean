import Mathlib
import P2M.Util
import P2M.Sol.S_IsReduced_tensorProduct_residueField_of_forall_isMaximal_adicCompletion

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem IsReduced.tensorProduct_residueField_of_forall_isMaximal_adicCompletion
    {A : Type} [CommRing A] [IsLocalRing A]
    {C : Type} [CommRing C] [Algebra A C] [IsNoetherianRing C]
    (h : ∀ x : Ideal C, x.IsMaximal →
      (maximalIdeal A).map (algebraMap A C) ≤ x →
      IsReduced (ResidueField A ⊗[A] AdicCompletion x C)) :
    IsReduced (ResidueField A ⊗[A] C) := by p2m_exact_reverting @_root_.P2MW.S_IsReduced_tensorProduct_residueField_of_forall_isMaximal_adicCompletion.solution
