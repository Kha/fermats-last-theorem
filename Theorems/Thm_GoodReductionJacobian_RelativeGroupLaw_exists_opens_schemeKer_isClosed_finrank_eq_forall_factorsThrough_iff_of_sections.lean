import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_isClosed_finrank_eq_forall_factorsThrough_iff_of_sections

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_schemeKer_isClosed_finrank_eq_forall_factorsThrough_iff_of_sections
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) [IsFinite (L.schemeKerStr n)] [Etale (L.schemeKerStr n)]
    {ι : Type} [Finite ι] (σ : ι → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hσ : ∀ i, nsmulPt L (𝟙 (Spec (CommRingCat.of R))) n (σ i) = L.one (𝟙 (Spec (CommRingCat.of R))))
    (hne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (τ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (i j : ι),
      τ ≫ (σ i).1 = τ ≫ (σ j).1 → i = j) :
    ∃ U : (L.schemeKer n).Opens,
      IsClosed (U : Set ↥(L.schemeKer n)) ∧
      (∀ s : ↥(Spec (CommRingCat.of R)), (U.ι ≫ L.schemeKerStr n).finrank s = Nat.card ι) ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
        FactorsThrough (U.ι ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) P ↔
          nsmulPt L t n P = L.one t ∧
            ∀ (k : Type u) [Field k] [IsAlgClosed k] (τ : Spec (CommRingCat.of k) ⟶ T),
              ∃ i, τ ≫ P.1 = (τ ≫ t) ≫ (σ i).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_schemeKer_isClosed_finrank_eq_forall_factorsThrough_iff_of_sections.solution
