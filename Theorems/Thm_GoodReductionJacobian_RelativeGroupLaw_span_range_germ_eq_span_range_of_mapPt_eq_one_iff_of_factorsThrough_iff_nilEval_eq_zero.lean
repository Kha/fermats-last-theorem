import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_span_range_germ_eq_span_range_of_mapPt_eq_one_iff_of_factorsThrough_iff_nilEval_eq_zero

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.span_range_germ_eq_span_range_of_mapPt_eq_one_iff_of_factorsThrough_iff_nilEval_eq_zero
    (k : Type) [Field k]

    {A : Scheme.{0}} {fA : A ⟶ Spec (CommRingCat.of k)} (LA : RelativeGroupLaw k fA)
    (FA : MvFormalGroup 2 k) (θA : RelativeGroupLaw.FormalCoordinates fA 2) (hθA : LA.IsFormalCoordinates FA θA)

    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of k)} (L' : RelativeGroupLaw k f')
    (F' : MvFormalGroup 2 k) (θ'' : RelativeGroupLaw.FormalCoordinates f' 2) (hθ'' : L'.IsFormalCoordinates F' θ'')

    (p : A ⟶ A') (hp : p ≫ f' = fA)
    (T : Series k) (hT : IsLawHom FA F' T)
    (hpT : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (θA B'' s).1 ≫ p = (θ'' B'' (fun i => MvFormalGroup.nilEval m (T i) s)).1)

    (γ : Series k) (hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0)

    (K : Scheme.{0}) (ι : K ⟶ A)
    (hp_ker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t fA),
      mapPt p hp P = L'.one t ↔ FactorsThrough ι P)
    (hKγ : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (FactorsThrough ι (θA B'' s) ↔ ∀ i, MvFormalGroup.nilEval n (γ i) s = 0)) :
    Ideal.span (Set.range T) = Ideal.span (Set.range γ) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_span_range_germ_eq_span_range_of_mapPt_eq_one_iff_of_factorsThrough_iff_nilEval_eq_zero.solution
