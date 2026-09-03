import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_algEquiv_kerAlgebra_apply_mk_eq_nilEval_of_isFormalCoordinates_of_forall_isInfinitesimal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld
  CerednikDrinfeld.SpecialFormal

theorem GoodReductionJacobian.RelativeGroupLaw.exists_algEquiv_kerAlgebra_apply_mk_eq_nilEval_of_isFormalCoordinates_of_forall_isInfinitesimal
    {B : Type} [CommRing B] [IsNoetherianRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f)
    (F : MvFormalGroup 2 B) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates F θ)
    (φ : Series B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (n : ℕ)

    (hφ : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (k : ℕ), J ^ (k + 1) = ⊥ →
      ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval k (φ i) s) = L.nsmul (Scheme.specOver (𝒪 := B) B') n (θ B' s))

    (hinf : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f),
      L.nsmul (Scheme.specOver (𝒪 := B) B') n P = L.one (Scheme.specOver (𝒪 := B) B') →
      ∃ J : Ideal B', IsNilpotent J ∧ L.IsInfinitesimal J P)

    (R : Type) [CommRing R] [Algebra B R] (e : Spec (CommRingCat.of R) ≅ L.schemeKer n)
    (he : e.hom ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap B R))) :
    ∃ (J : Ideal R) (ν : ℕ) (s₀ : Fin 2 → R), J ^ (ν + 1) = ⊥ ∧ 1 ≤ ν ∧ (∀ i, s₀ i ∈ J) ∧
      (θ R s₀).1 = e.hom ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ∧
      ∃ E : (MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range φ)) ≃ₐ[B] R,
        ∀ G : MvPowerSeries (Fin 2) B, E (Ideal.Quotient.mk _ G) = MvFormalGroup.nilEval ν G s₀ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_algEquiv_kerAlgebra_apply_mk_eq_nilEval_of_isFormalCoordinates_of_forall_isInfinitesimal.solution
