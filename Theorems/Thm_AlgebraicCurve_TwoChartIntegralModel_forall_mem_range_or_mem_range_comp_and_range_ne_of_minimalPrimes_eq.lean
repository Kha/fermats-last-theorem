import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_forall_mem_range_or_mem_range_comp_and_range_ne_of_minimalPrimes_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicCurve.TwoChartIntegralModel.forall_mem_range_or_mem_range_comp_and_range_ne_of_minimalPrimes_eq
    (R : Type u) [CommRing R]
    (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (F₀ : Type u) [Field F₀] [Algebra R F₀] (j₀ : F₀) [Fact (j₀ ≠ 0)]

    (w : TwoChartIntegralModel R F j ≅ TwoChartIntegralModel R F j) (hw : w.hom ≫ toBase R F j = toBase R F j)
    (theta : ↥(chartAlgFin R F j) ≃ₐ[R] ↥(chartAlgFin R F j))
    (hwchart : ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin R F j)

    (κ : Type u) [Field κ] [Algebra R κ]

    (wκ : pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hwκfst : wκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ w.hom)
    (hwκsnd : wκ ≫ pullback.snd _ _ = pullback.snd _ _)

    (c₀ : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F₀ j₀))) ⟶
      pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F₀ j₀))).toRingHom) ≫ ιFin R F₀ j₀)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F₀ j₀)))))
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j)))))

    (σ₀ : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] κ ⊗[R] ↥(chartAlgFin R F₀ j₀))
    (hσ₀ : Function.Surjective σ₀)
    (hmin : minimalPrimes (κ ⊗[R] ↥(chartAlgFin R F j)) =
      {RingHom.ker σ₀.toRingHom,
       Ideal.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) (theta : _ →ₐ[R] _)).toRingHom (RingHom.ker σ₀.toRingHom)})
    (hne : RingHom.ker σ₀.toRingHom ≠
      Ideal.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) (theta : _ →ₐ[R] _)).toRingHom (RingHom.ker σ₀.toRingHom))

    (comp₀ : pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcomp₀_over : comp₀ ≫ pullback.snd _ _ = pullback.snd _ _) (hcomp₀_ci : IsClosedImmersion comp₀)
    (hcomp₀_chart : c₀ ≫ comp₀ = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c)
    (hcomp₀_match : ∀ x, comp₀.base x ∈ Set.range c.base → x ∈ Set.range c₀.base)

    (hdense : Dense (Set.range c.base)) :
    (∀ y : ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))),
        y ∈ Set.range comp₀.base ∨ y ∈ Set.range (comp₀ ≫ wκ).base) ∧
      Set.range comp₀.base ≠ Set.range (comp₀ ≫ wκ).base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_mem_range_or_mem_range_comp_and_range_ne_of_minimalPrimes_eq.solution
