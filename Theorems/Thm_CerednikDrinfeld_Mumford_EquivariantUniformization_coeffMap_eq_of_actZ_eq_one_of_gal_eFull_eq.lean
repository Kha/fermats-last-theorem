import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
    {E V : Type} [Fintype E] [DecidableEq V]
    {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {S : Type} [Group S]
    {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal)
    (σ : S) (hσ : actZ σ = 1)
    (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion)
    (hs : ∀ c, s c = (scalar σ) • c)
    (hiso : ∀ c, Valued.v (s c) = Valued.v c)
    (u : 𝒰.P.TorusPoints) (hu : gal σ (𝒰.eFull u) = 𝒰.eFull u) :
    𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq.solution
