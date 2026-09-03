import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq
    {E V : Type} [Fintype E] [DecidableEq V]
    {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    [Fact (A.DecompositionIsometric ℚ)]
    {T : Type} [AddCommGroup T] {S : Type} [Group S]
    {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal)
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)
    (hι_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        actZ (ι τ) = 1)
    (u : 𝒰.P.TorusPoints)
    (hu : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        gal (ι τ) (𝒰.eFull u) = 𝒰.eFull u)
    (τ : ↥(A.decompositionSubgroup ℚ))
    (hτ : (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ)
    (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion) (hs : ∀ c, s c = τ • c) :
    𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq.solution
