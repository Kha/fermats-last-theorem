import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_comp_eq_comp_of_finiteType_of_directedSystem

set_option autoImplicit false
theorem RingHom.exists_comp_eq_comp_of_finiteType_of_directedSystem
    (ι : Type) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Type) [∀ i, CommRing (S i)]
    (t : ∀ i j, i ≤ j → (S i →+* S j))
    (ht₁ : ∀ i (h : i ≤ i), t i i h = RingHom.id (S i))
    (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
    (L : Type) [CommRing L] (c : ∀ i, S i →+* L)
    (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
    (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
    (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z)
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R]
    (i : ι) (ψ ψ' : R →+* S i) (h : (c i).comp ψ = (c i).comp ψ') :
    ∃ (j : ι) (hij : i ≤ j), (t i j hij).comp ψ = (t i j hij).comp ψ' := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_comp_eq_comp_of_finiteType_of_directedSystem.solution
