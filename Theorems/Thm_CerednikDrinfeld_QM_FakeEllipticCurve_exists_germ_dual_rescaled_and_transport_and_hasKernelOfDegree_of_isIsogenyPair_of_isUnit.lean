import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_germ_dual_rescaled_and_transport_and_hasKernelOfDegree_of_isIsogenyPair_of_isUnit
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_germ_dual_rescaled_and_transport_and_hasKernelOfDegree_of_isIsogenyPair_of_isUnit
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (K₀ : Type) [Field K₀] [CharZero K₀]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ β₀' : Series (Onr ⧸ pIdeal r Onr)) (N₀ : ℕ)
    (E₀ : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀) (hE₀ : Function.Injective E₀)
    (E_X : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hAd : ∀ ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
      ∃ e : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})),
        (e : MvFormalGroup.End Φ.F).toPowerSeries =
          β₀'.comp ((Series.map κ (ε : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
        E₀ e = ((r : K₀) ^ N₀) • E_X ε)

    (f f' : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (d v : ℕ) (hv : IsUnit ((v : ℕ) : Zp2 r))
    (hff' : FakeEllipticCurve.IsIsogenyPair (v * r ^ d) A₀ A₀ f f')
    (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})))
    (hε : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
      J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) = mapPt f hf (θ₀ B' s)) :
    ∃ (hf' : f' ≫ A₀.f = A₀.f) (ε' ε'' : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})))
      (e e'' : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) (m' : ℕ),
      (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
        J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε' : MvFormalGroup.End X₀.F).toPowerSeries i) s) = mapPt f' hf' (θ₀ B' s)) ∧
      (ε'' : MvFormalGroup.End X₀.F) = (ε' : MvFormalGroup.End X₀.F) * X₀.actEnd ((hv.unit⁻¹ : (Zp2 r)ˣ) : Zp2 r) ∧
      ε * ε'' = ((r ^ d : ℕ) : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) ∧
      ε'' * ε = ((r ^ d : ℕ) : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) ∧
      (e : MvFormalGroup.End Φ.F).toPowerSeries =
        β₀'.comp ((Series.map κ (ε : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
      (e'' : MvFormalGroup.End Φ.F).toPowerSeries =
        β₀'.comp ((Series.map κ (Series.comp (ε' : MvFormalGroup.End X₀.F).toPowerSeries
          (X₀.act ((hv.unit⁻¹ : (Zp2 r)ˣ) : Zp2 r)))).comp β₀) ∧
      E₀ e = ((r : K₀) ^ N₀) • E_X ε ∧ E₀ e'' = ((r : K₀) ^ N₀) • E_X ε'' ∧
      e * e'' = ((r ^ (2 * N₀ + d) : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) ∧
      FormalODModule.HasKernelOfDegree ((e'' : MvFormalGroup.End Φ.F).toPowerSeries) (r ^ (2 * m')) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_germ_dual_rescaled_and_transport_and_hasKernelOfDegree_of_isIsogenyPair_of_isUnit.solution
