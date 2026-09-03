import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_exists_ringHom_comp_eq_val_of_fg_of_directedSystem

set_option autoImplicit false
theorem Subalgebra.exists_ringHom_comp_eq_val_of_fg_of_directedSystem
    (ι : Type) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Type) [∀ i, CommRing (S i)]
    (t : ∀ i j, i ≤ j → (S i →+* S j))
    (ht₁ : ∀ i (h : i ≤ i), t i i h = RingHom.id (S i))
    (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
    (L : Type) [CommRing L] (c : ∀ i, S i →+* L)
    (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
    (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
    (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z)
    (T : Subalgebra ℤ L) (hT : T.FG) :
    (∀ i₀ : ι, ∃ (j : ι) (_ : i₀ ≤ j) (ψ : ↥T →+* S j), (c j).comp ψ = T.val.toRingHom) ∧
    (∀ (i : ι) (ψ ψ' : ↥T →+* S i), (c i).comp ψ = (c i).comp ψ' →
        ∃ (j : ι) (h : i ≤ j), (t i j h).comp ψ = (t i j h).comp ψ') := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_exists_ringHom_comp_eq_val_of_fg_of_directedSystem.solution
