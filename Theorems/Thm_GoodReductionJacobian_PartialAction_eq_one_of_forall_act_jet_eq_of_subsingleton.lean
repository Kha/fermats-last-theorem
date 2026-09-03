import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_PartialAction_eq_one_of_forall_act_jet_eq_of_subsingleton
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.PartialAction.eq_one_of_forall_act_jet_eq_of_subsingleton
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (x : SchemeHomOver t f)
    (hx : ∀ (n : ℕ)
      (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
          IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ n))
          ⟶ P),
      jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _ →
      ∃ hd : a.Defined
          (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
          (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
        (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) :
    x = L.one t := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_PartialAction_eq_one_of_forall_act_jet_eq_of_subsingleton.solution
