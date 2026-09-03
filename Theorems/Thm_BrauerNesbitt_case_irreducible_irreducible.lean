import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_BrauerNesbitt_case_irreducible_irreducible

theorem BrauerNesbitt.case_irreducible_irreducible {k : Type*} {G : Type*} {V₁ : Type*}
  {V₂ : Type*} [Field k] [Monoid G] [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁] [AddCommGroup V₂]
  [Module k V₂] [FiniteDimensional k V₂] (ρ₁ : Representation k G V₁) (ρ₂ : Representation k G V₂)
  [IsAlgClosed k] [ρ₁.IsIrreducible] [ρ₂.IsIrreducible]
  (htr : ∀ (g : G), (LinearMap.trace k V₁) (ρ₁ g) = (LinearMap.trace k V₂) (ρ₂ g)) :
  ∃ e : V₁ ≃ₗ[k] V₂, ∀ (g : G) (v : V₁), e ((ρ₁ g) v) = (ρ₂ g) (e v) := by p2m_exact_reverting @_root_.P2MW.S_BrauerNesbitt_case_irreducible_irreducible.solution
