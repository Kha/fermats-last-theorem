import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph
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
    (γ : ↥((pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).image))
    (hγ : ((pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).imageι ≫
          pullback.fst g h).base γ = η) :
    ∃ (V : G.Opens) (v : (V : Scheme.{u}) ⟶ H),
      v ≫ h = V.ι ≫ g ∧
      (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      η ∈ V ∧
      ∃ hle : Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⊆
          Set.range V.ι.base,
        IsOpenImmersion.lift V.ι (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hle ≫ v =
          φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph.solution
