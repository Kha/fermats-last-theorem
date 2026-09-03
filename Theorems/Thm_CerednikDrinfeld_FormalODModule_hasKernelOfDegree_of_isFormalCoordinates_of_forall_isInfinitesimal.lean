import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_isFormalCoordinates_of_forall_isInfinitesimal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasKernelOfDegree_of_isFormalCoordinates_of_forall_isInfinitesimal
    {B : Type} [CommRing B] [IsNoetherianRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f)
    (F : MvFormalGroup 2 B) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates F θ)
    (φ : Series B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (n : ℕ) (hn : 0 < n)

    (hφ : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (k : ℕ), J ^ (k + 1) = ⊥ →
      ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval k (φ i) s) = L.nsmul (Scheme.specOver (𝒪 := B) B') n (θ B' s))

    (d : ℕ) [IsFinite (L.schemeKerStr n)] [Flat (L.schemeKerStr n)] [LocallyOfFinitePresentation (L.schemeKerStr n)]
    (hrank : ∀ s : ↥(Spec (CommRingCat.of B)), (L.schemeKerStr n).finrank s = d)

    (hinf : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f),
      L.nsmul (Scheme.specOver (𝒪 := B) B') n P = L.one (Scheme.specOver (𝒪 := B) B') →
      ∃ J : Ideal B', IsNilpotent J ∧ L.IsInfinitesimal J P) :
    FormalODModule.HasKernelOfDegree φ d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_isFormalCoordinates_of_forall_isInfinitesimal.solution
