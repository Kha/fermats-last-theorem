import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero
attribute [-simp] ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

open Polynomial groupCohomology ExtCitation

theorem ResidualGaloisRep.exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hsplit : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∃ α β : k, LinearMap.charpoly (ρbar.ρ σ) = (X - C α) * (X - C β))
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    [Module (ZMod p) (LinearMap.ker (LinearMap.trace k ρbar.V))]
    (ρ₀ : Representation (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (LinearMap.ker (LinearMap.trace k ρbar.V)))
    (hρ₀ : ∀ g v, ρ₀ g v = ρbar.adZeroRep g v)
    {n : ℕ} (hn : 0 < n) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (p ^ n))
    (c : cocycles₁ ((Rep.of ρ₀).dualTwist (cycloChar p)))
    (hc : H1π ((Rep.of ρ₀).dualTwist (cycloChar p)) c ≠ 0) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      τ ζ = ζ ∧ ρbar.adZeroRep τ = 1 ∧ c τ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero.solution
