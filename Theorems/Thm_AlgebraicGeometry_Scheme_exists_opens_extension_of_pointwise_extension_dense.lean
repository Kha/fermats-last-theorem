import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_pointwise_extension_dense

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.exists_opens_extension_of_pointwise_extension_dense
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) (h : H ⟶ Spec (CommRingCat.of R))
    [IsIntegral G] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]

    (η : G) (hη : g.base η = IsLocalRing.closedPoint R)
    (hirr : ∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x)
    [IsDiscreteValuationRing (G.presheaf.stalk η)]

    (φK : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
      pullback h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hφK : φK ≫ pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R K))))

    (D : Set G) (hD : ∀ z ∈ D, g.base z = IsLocalRing.closedPoint R) (hDη : η ∈ closure D)
    (hpts : ∀ z ∈ D, ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A)
        (c : Spec (CommRingCat.of A) ⟶ pullback g h),
        (c ≫ pullback.fst g h).base (IsLocalRing.closedPoint A) = z ∧
        c.base ⟨⊥, Ideal.isPrime_bot⟩ ∈ Set.range
          (pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).base) :
    ∃ (V : G.Opens) (v : (V : Scheme.{u}) ⟶ H),
      v ≫ h = V.ι ≫ g ∧
      (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      η ∈ V ∧

      ∃ hle : Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⊆
          Set.range V.ι.base,
        IsOpenImmersion.lift V.ι (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hle ≫ v =
          φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_pointwise_extension_dense.solution
