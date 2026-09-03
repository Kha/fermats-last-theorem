import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_DRLevel_forall_mem_range_or_mem_range_and_range_ne_of_minimalPrimes_eq
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped TensorProduct

theorem ModularCurve.DRLevel.forall_mem_range_or_mem_range_and_range_ne_of_minimalPrimes_eq
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]

    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hwchart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] [Algebra (DRLevel.R q) κ]

    (c₀ : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶
      DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))))
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))))

    (σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))
    (hσ₀ : Function.Surjective σ₀)
    (hmin : minimalPrimes (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) =
      {RingHom.ker σ₀.toRingHom,
       Ideal.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) (theta : _ →ₐ[DRLevel.R q] _)).toRingHom (RingHom.ker σ₀.toRingHom)})
    (hne : RingHom.ker σ₀.toRingHom ≠
      Ideal.comap (Algebra.TensorProduct.map (AlgHom.id κ κ) (theta : _ →ₐ[DRLevel.R q] _)).toRingHom (RingHom.ker σ₀.toRingHom))

    (comp₀ : DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hcomp₀_over : comp₀ ≫ pullback.snd _ _ = pullback.snd _ _) (hcomp₀_ci : IsClosedImmersion comp₀)
    (hcomp₀_chart : c₀ ≫ comp₀ = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c)
    (hcomp₀_match : ∀ x, comp₀.base x ∈ Set.range c.base → x ∈ Set.range c₀.base)

    (hdense : Dense (Set.range c.base)) :
    (∀ y : DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ),
        y ∈ Set.range comp₀.base ∨ y ∈ Set.range (comp₀ ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ)).base) ∧
      Set.range comp₀.base ≠ Set.range (comp₀ ≫ DRLevel.fibreMap w.hom hw (algebraMap (DRLevel.R q) κ)).base := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRLevel_forall_mem_range_or_mem_range_and_range_ne_of_minimalPrimes_eq.solution
