import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false
universe u
open Module
theorem Representation.finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree
    {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ p ∣ Fintype.card Δ)
    {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A) (htf : ∀ a : A, p • a = 0 → a = 0)
    (B : AddSubgroup A) [B.FiniteIndex] (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) Δ VN)
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] [FiniteDimensional (ZMod p) VA]
    (PA : Representation (ZMod p) Δ VA)
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a)
    (hπAΔ : ∀ (d : Δ) (a : A), πA (act d a) = PA d (πA a))
    {VB : Type*} [AddCommGroup VB] [Module (ZMod p) VB] [FiniteDimensional (ZMod p) VB]
    (PB : Representation (ZMod p) Δ VB)
    (πB : B →+ VB) (hπB : Function.Surjective πB) (hkerB : ∀ b : B, πB b = 0 ↔ ∃ b' : B, p • b' = b)
    (hπBΔ : ∀ (d : Δ) (b : B), πB ⟨act d b, hB d b b.2⟩ = PB d (πB b)) :
    finrank (ZMod p) (N.linHom PA).invariants = finrank (ZMod p) (N.linHom PB).invariants := by p2m_exact_reverting @_root_.P2MW.S_Representation_finrank_invariants_linHom_eq_of_finiteIndex_of_torsionFree.solution
