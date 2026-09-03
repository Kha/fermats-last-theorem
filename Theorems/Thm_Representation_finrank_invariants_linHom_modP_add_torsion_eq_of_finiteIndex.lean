import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false
universe u
open Module
theorem Representation.finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex
    {p : ℕ} [Fact p.Prime] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : ¬ p ∣ Fintype.card Δ)
    {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A)
    (B : AddSubgroup A) [B.FiniteIndex] (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
    {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
    (N : Representation (ZMod p) Δ VN)
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] [FiniteDimensional (ZMod p) VA]
    (PA : Representation (ZMod p) Δ VA)
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a)
    (hπAΔ : ∀ (d : Δ) (a : A), πA (act d a) = PA d (πA a))
    {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA] [FiniteDimensional (ZMod p) WA]
    (TA : Representation (ZMod p) Δ WA)
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0)
    (hιAΔ : ∀ (d : Δ) (w : WA), ιA (TA d w) = act d (ιA w))
    {VB : Type*} [AddCommGroup VB] [Module (ZMod p) VB] [FiniteDimensional (ZMod p) VB]
    (PB : Representation (ZMod p) Δ VB)
    (πB : B →+ VB) (hπB : Function.Surjective πB) (hkerB : ∀ b : B, πB b = 0 ↔ ∃ b' : B, p • b' = b)
    (hπBΔ : ∀ (d : Δ) (b : B), πB ⟨act d b, hB d b b.2⟩ = PB d (πB b))
    {WB : Type*} [AddCommGroup WB] [Module (ZMod p) WB] [FiniteDimensional (ZMod p) WB]
    (TB : Representation (ZMod p) Δ WB)
    (ιB : WB →+ B) (hιB : Function.Injective ιB) (hranB : ∀ b : B, b ∈ Set.range ιB ↔ p • b = 0)
    (hιBΔ : ∀ (d : Δ) (w : WB), (ιB (TB d w) : A) = act d (ιB w)) :
    finrank (ZMod p) (N.linHom PA).invariants + finrank (ZMod p) (N.linHom TB).invariants
      = finrank (ZMod p) (N.linHom PB).invariants + finrank (ZMod p) (N.linHom TA).invariants := by p2m_exact_reverting @_root_.P2MW.S_Representation_finrank_invariants_linHom_modP_add_torsion_eq_of_finiteIndex.solution
