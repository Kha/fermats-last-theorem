import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_eq_algebraMap_of_hasValue_pair_of_generalPosition

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.exists_eq_algebraMap_of_hasValue_pair_of_generalPosition
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (S : Finset (Place k F × Place k F)) (E₁ E₂ : Finset (Place k F))
    (hgp₁ : ∀ h : F,
      (∀ v : Place k F, v ∉ E₁ → 0 ≤ v.ord h) → (∀ v ∈ E₁, -1 ≤ v.ord h) →
      (∀ s ∈ S, s.1.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : F,
      (∀ v : Place k F, v ∉ E₂ → 0 ≤ v.ord h) → (∀ v ∈ E₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k F c)
    (h₁ h₂ : F)
    (hh₁ : ∀ v : Place k F, v ∉ E₁ → 0 ≤ v.ord h₁) (hh₁' : ∀ v ∈ E₁, -1 ≤ v.ord h₁)
    (hh₂ : ∀ v : Place k F, v ∉ E₂ → 0 ≤ v.ord h₂) (hh₂' : ∀ v ∈ E₂, -1 ≤ v.ord h₂)
    (hval : ∀ s ∈ S, ∃ c : k, s.1.HasValue h₁ c ∧ s.2.HasValue h₂ c) :
    ∃ c : k, h₁ = algebraMap k F c ∧ h₂ = algebraMap k F c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_eq_algebraMap_of_hasValue_pair_of_generalPosition.solution
