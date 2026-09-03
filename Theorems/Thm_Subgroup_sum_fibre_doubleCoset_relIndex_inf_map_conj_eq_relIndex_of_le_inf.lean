import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex_of_le_inf

set_option autoImplicit false

open MulAction

theorem Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex_of_le_inf
    {G : Type*} [Group G] (H K K₁ K₂ K₁₂ : Subgroup G) (hK₁ : K₁ ≤ K) (hK₂ : K₂ ≤ K)
    (h₁ : K₁₂ ≤ K₁) (h₂ : K₁₂ ≤ K₂) (hinf : K₁ ⊓ K₂ ≤ K₁₂)
    (hsurj : ∀ k : K, ∃ k₁ : K₁, ((k₁ : G)⁻¹ * k) ∈ K₂)
    (z y : G) (hyz : DoubleCoset.mk H K z = DoubleCoset.mk H K y)
    [K₂.IsFiniteRelIndex K] [K₁₂.IsFiniteRelIndex K₁]
    [Fintype {c : DoubleCoset.Quotient (H : Set G) (K₁₂ : Set G) //
      DoubleCoset.mk H K₂ c.out = DoubleCoset.mk H K₂ y ∧ DoubleCoset.mk H K₁ c.out = DoubleCoset.mk H K₁ z}] :
    ∑ c : {c : DoubleCoset.Quotient (H : Set G) (K₁₂ : Set G) //
        DoubleCoset.mk H K₂ c.out = DoubleCoset.mk H K₂ y ∧ DoubleCoset.mk H K₁ c.out = DoubleCoset.mk H K₁ z},
      (H ⊓ K₁₂.map (MulAut.conj c.1.out).toMonoidHom).relIndex (H ⊓ K₁.map (MulAut.conj c.1.out).toMonoidHom) =
        (H ⊓ K₂.map (MulAut.conj y).toMonoidHom).relIndex (H ⊓ K.map (MulAut.conj y).toMonoidHom) := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex_of_le_inf.solution
