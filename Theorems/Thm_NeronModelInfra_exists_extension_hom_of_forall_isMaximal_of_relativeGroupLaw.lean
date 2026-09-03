import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw
set_option autoImplicit false
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~existsUnique_extension_of_exists_isLocalization_atPrime GoodReductionJacobian"
theorem NeronModelInfra.exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [IsSeparated g] [LocallyOfFiniteType g] [Flat g]
    (L : RelativeGroupLaw ℤ g)
    (φη : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))))
    (hhom : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ))
        (x y : SchemeHomOver s (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))),
      NeronModelInfra.schemeHomOverComp
          ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s x y) φη =
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    {ι' : Type} (a b : ι' → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ G))
    (hab : ∀ (i : ι') (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
      z ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = a i →
      zt ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = b i →
      zt = z ≫ φη.1)
    (ha : ∀ i : ι', a i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hb : ∀ i : ι', b i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (h : ∀ (𝔪 : Ideal ℤ) [𝔪.IsMaximal], ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℤ A)
        (_ : IsLocalization.AtPrime A 𝔪) (_ : Algebra A ℚ) (_ : IsScalarTower ℤ A ℚ)
        (gA : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ⟶ G),
        gA ≫ g = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ≫ g ∧
        ∀ j : pullback g (specGenericFibreInclusion ℤ ℚ) ⟶
            pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))),
          j ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) =
            pullback.fst g (specGenericFibreInclusion ℤ ℚ) →
          j ≫ gA = φη.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ)) :
    ∃ φ : SchemeHomOver g g,
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ≫ φ.1 =
        φη.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s g),
        NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
          L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ i : ι', b i = a i ≫ φ.1 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw.solution
