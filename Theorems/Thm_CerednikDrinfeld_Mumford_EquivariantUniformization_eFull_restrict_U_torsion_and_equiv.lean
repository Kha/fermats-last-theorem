import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_EquivariantUniformization_eFull_restrict_U_torsion_and_equiv
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford ModularCurve

theorem CerednikDrinfeld.Mumford.EquivariantUniformization.eFull_restrict_U_torsion_and_equiv
    {E V : Type} [Fintype E] [DecidableEq V] {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {S : Type} [Group S] {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal) :
    (∀ t : T, IsOfFinAddOrder t → t ∈ (𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom).range) ∧
    (∀ u : ↥𝒰.P.U, IsOfFinAddOrder ((𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom) u)) ∧
    (∀ u : ↥𝒰.P.U, (𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom) u = 0 ↔ (u : 𝒰.P.TorusPoints) ∈ 𝒰.P.periodLattice) ∧
    (∀ σ : S, actZ σ = 1 → ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = (scalar σ) • c) →
      ∀ (u : ↥𝒰.P.U) (hu : 𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : 𝒰.P.TorusPoints) ∈ 𝒰.P.U),
        (𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom) ⟨𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : 𝒰.P.TorusPoints), hu⟩ =
          gal σ ((𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom) u)) ∧
    (∀ σ : S, actZ σ = 1 → ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = (scalar σ) • c) →
      ∀ u : 𝒰.P.TorusPoints,
        𝒰.eFull (𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u) = gal σ (𝒰.eFull u)) ∧
    (∀ σ : S, actZ σ = 1 → ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = (scalar σ) • c) →
      ∀ x y : ↥(ribbonKernel D),
        s (((Additive.toMul (𝒰.P.Q x y) : (↥𝒰.K)ˣ) : ↥𝒰.K) : A.valuation.Completion) =
          (((Additive.toMul (𝒰.P.Q x y) : (↥𝒰.K)ˣ) : ↥𝒰.K) : A.valuation.Completion)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_eFull_restrict_U_torsion_and_equiv.solution
