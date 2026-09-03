import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_exists_basis_span_eq_of_filtration
open IsLocalRing Submodule
theorem TateModule.exists_basis_span_eq_of_filtration
    {M : Type} [AddCommGroup M] {p : ℕ} [Fact p.Prime]
    (hcard : ∀ n, Nat.card (torsionBy ℤ M ((p^n : ℕ) : ℤ)) = (p^n)^2)
    (F : ℕ → AddSubgroup M) (P : M → Prop)
    (hFiff : ∀ m, 1 ≤ m → ∀ x, x ∈ F m ↔ ((p^m : ℕ) : ℤ) • x = 0 ∧ P x)
    (hFcard : ∀ m, 1 ≤ m → Nat.card (F m) = p^m)
    (L : Submodule ℤ_[p] (TateModule p M))
    (hL : ∀ x, x ∈ L ↔ ∀ m, 1 ≤ m → (x : ℕ → M) m ∈ F m) :
    ∃ b : Module.Basis (Fin 2) ℤ_[p] (TateModule p M), L = ℤ_[p] ∙ b 0 := by p2m_exact_reverting @_root_.P2MW.S_TateModule_exists_basis_span_eq_of_filtration.solution
