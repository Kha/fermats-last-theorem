import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (c : UpperHalfPlane →₀ ℤ)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : UpperHalfPlane, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((Nat.card (MulAction.stabilizer
            (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) / 2 : ℕ) *
        Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane)) c
          (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) τ) : ℤ) : WithTop ℤ)) :
    (c.sum fun τ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf Γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer.solution
