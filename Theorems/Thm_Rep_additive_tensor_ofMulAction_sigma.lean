import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_additive_tensor_ofMulAction_sigma
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.additive_tensor_ofMulAction_sigma
    {k : Type} [Field k] {G : Type} [Group G]
    (ψ : Rep.{0} k G → ℤ)
    (hadd : ∀ (X : ShortComplex (Rep.{0} k G)), X.ShortExact →
      FiniteDimensional k X.X₂ → ψ X.X₂ = ψ X.X₁ + ψ X.X₃)
    (M : Rep.{0} k G) [FiniteDimensional k M]
    {ι : Type} [Fintype ι] (X : ι → Type) [∀ i, MulAction G (X i)] [∀ i, Finite (X i)] :
    ψ (M ⊗ Rep.ofMulActionFinsupp k G (Σ i, X i)) = ∑ i, ψ (M ⊗ Rep.ofMulActionFinsupp k G (X i)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_additive_tensor_ofMulAction_sigma.solution
