import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isODHom_isRigTransport_of_isFormalModuleVia
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isODHom_isRigTransport_of_isFormalModuleVia
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

    (coord : ↥Λ → Zp2 r × Zp2 r)
    (hdense : ∀ (k : ℕ) (α β : Zp2 r), ∃ m : ↥Λ,
      (coord m).1 - α ∈ Ideal.span {((r : Zp2 r)) ^ k} ∧ (coord m).2 - β ∈ Ideal.span {((r : Zp2 r)) ^ k})

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]

    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))

    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hE : E.IsFormalModuleVia coord X θ) :
    ∃ (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ pIdeal r B))
      (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})),

      κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (pIdeal r B) ∧
      κB.comp (Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* B)).comp κ ∧

      FormalODModule.IsODHom (X₀.map (Rigidification.residueLeg π ψ))
        (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) σ ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
          [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
          algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
          algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
            (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Rigidification.residueLeg π ψ) →
          ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
              PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
              PA ≫ ρ.gA = (θ₀ B'' s).1 →
                PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1) ∧

      ∀ (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (j n : ℕ),
        Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j
          ({ X := X, n := n,
             ρ := (Series.map κB σ).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
               (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j))) } :
            Rigidified r Φ B) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isODHom_isRigTransport_of_isFormalModuleVia.solution
