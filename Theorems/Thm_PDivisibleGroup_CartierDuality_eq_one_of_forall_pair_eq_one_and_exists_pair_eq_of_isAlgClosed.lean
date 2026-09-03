import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
    (v : ℕ) :
    (∀ f : G.Point K v, (∀ ψ : G'.Point K v, D.pair K v f ψ = 1) → f = 1) ∧
    (∀ ψ : G'.Point K v, (∀ f : G.Point K v, D.pair K v f ψ = 1) → ψ = 1) ∧
    (∀ χ : G'.Point K v →* Kˣ, ∃ f : G.Point K v, ∀ ψ : G'.Point K v, D.pair K v f ψ = χ ψ) ∧
    (∀ χ : G.Point K v →* Kˣ, ∃ ψ : G'.Point K v, ∀ f : G.Point K v, D.pair K v f ψ = χ f) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_eq_one_of_forall_pair_eq_one_and_exists_pair_eq_of_isAlgClosed.solution
