import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsInvariant_exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq

theorem Algebra.IsInvariant.exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    {Ω : Type*} [Field Ω] (φ₁ φ₂ : B →+* Ω)
    (h : φ₁.comp (algebraMap A B) = φ₂.comp (algebraMap A B)) :
    ∃ g : G, φ₂ = φ₁.comp (MulSemiringAction.toRingHom G B g) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsInvariant_exists_ringHom_eq_comp_toRingHom_of_comp_algebraMap_eq.solution
