import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    (H : Type) [CommRing H] [Bialgebra R H]
    (H_W : Type) [CommRing H_W] [Bialgebra R H_W] (π : H →ₐc[R] H_W)
    (P : Type) [CommRing P] [Algebra R P] (qa : H →ₐ[R] P)
    (htors : ∀ (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C),
      ∃! c : H_W →ₐ[R] C,
        WithConv.toConv (a.comp qa) =
          WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa))
    (u : Spec (CommRingCat.of H_W) ⟶ N) (hu : u ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R H_W)))
    (hmul : ∀ (C : Type) [CommRing C] [Algebra R C] (φ ψ : H_W →ₐ[R] C)
        (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R C))) gN),
      x.1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ u →
      y.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ u →
      (L.mul _ x y).1 =
        Spec.map (CommRingCat.ofHom (WithConv.ofConv (WithConv.toConv φ * WithConv.toConv ψ)).toRingHom) ≫ u)
    (q : Spec (CommRingCat.of P) ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    ∃ g : SchemeHomOver (pullback.fst q q ≫ q) gN,
      L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
          (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
                Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
          (by
            simp only [Category.assoc]
            rw [← pullback.condition (f := q) (g := q),
              ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
              ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
              ← pullback.condition (f := q) (g := q)]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g ∧
      ∀ (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C) (c : H_W →ₐ[R] C),
        WithConv.toConv (a.comp qa) =
          WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa) →
        ∀ ab : Spec (CommRingCat.of C) ⟶ pullback q q,
          ab ≫ pullback.fst q q = Spec.map (CommRingCat.ofHom a.toRingHom) →
          ab ≫ pullback.snd q q = Spec.map (CommRingCat.ofHom b.toRingHom) →
          ab ≫ g.1 = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq.solution
