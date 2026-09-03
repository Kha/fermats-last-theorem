import Mathlib
import P2M.Util
import P2M.Sol.S_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian

universe u w
theorem HopfOrder.exists_greatest_of_sup_closed_of_le_noetherian
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (P : Subalgebra R A → Prop) (hsup : ∀ S S', P S → P S' → P (S ⊔ S'))
    (M : Subalgebra R A) [IsNoetherian R M] (hle : ∀ S, P S → S ≤ M) (h0 : ∃ S, P S) :
    ∃ S, P S ∧ ∀ S', P S' → S' ≤ S := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_exists_greatest_of_sup_closed_of_le_noetherian.solution
