import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_etale_preimage_snd_action_of_etale_nhds
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S' : Scheme.{u}) (j' : S' ⟶ G) [LocallyOfFiniteType (j' ≫ f)]
    (eS : Spec (CommRingCat.of k) ⟶ S') (heS : eS ≫ j' ≫ f = 𝟙 _)
    (W : (pullback (i ≫ f) (j' ≫ f)).Opens)
    (hzW : pullback.lift (LN.one (𝟙 _)).1 eS ((LN.one (𝟙 _)).2.trans heS.symm) (IsLocalRing.closedPoint k) ∈ W)
    (hW : Etale (W.ι ≫ (pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))) :
    ∃ S₀ : S'.Opens, eS (IsLocalRing.closedPoint k) ∈ S₀ ∧
      Etale ((pullback.snd (i ≫ f) (j' ≫ f) ⁻¹ᵁ S₀).ι ≫ (pullback.map (i ≫ f) (j' ≫ f) (i ≫ f) f (𝟙 N) j' (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds.solution
