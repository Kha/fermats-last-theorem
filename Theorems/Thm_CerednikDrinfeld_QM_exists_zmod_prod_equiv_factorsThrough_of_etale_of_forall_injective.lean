import Definitions.Def_CerednikDrinfeld_QMModuli
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (N : ℕ) (hN : IsUnit ((N : ℕ) : R))
    {C : Scheme.{u}} (lev : C ⟶ 𝒜) [IsClosedImmersion lev] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)]
    (lev_sub : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      FactorsThrough lev P → FactorsThrough lev Q →
        FactorsThrough lev (L.mul t P Q) ∧ FactorsThrough lev (L.inv t P))
    (lev_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), FactorsThrough lev (L.one t))
    (lev_torsion : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      FactorsThrough lev P → nsmulPt L t N P = L.one t)
    (lev_rank : ∀ s : ↥(Spec (CommRingCat.of R)), (lev ≫ f).finrank s = N ^ 2)
    (hgen : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), Function.Injective sk →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y)) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f // FactorsThrough lev P},
        ∀ x y : ZMod N × ZMod N,
          (e (x + y) : SchemeHomOver (geomPoint k sk) f) = L.mul (geomPoint k sk) (e x) (e y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_zmod_prod_equiv_factorsThrough_of_etale_of_forall_injective.solution
