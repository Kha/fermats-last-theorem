import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel~exists_hom_of_mem_chartAlgFin_of_forall_pow_mul_mem"

theorem AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j j' : F) [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)] [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j')]
    [IsSeparated (toBase R F j)] [IsSeparated (toBase R F j')]
    [Algebra.FiniteType R (chartAlgInf R F j)] [Algebra.FiniteType R (chartAlgInf R F j')]
    (hfin : j' ∈ chartAlgFin R F j) (hfin' : j ∈ chartAlgFin R F j')
    (hvis : ∀ y ∈ chartAlgInf R F j', ∃ s ∈ chartAlgInf R F j,
      (∃ a ∈ chartAlgInf R F j, s = 1 + j⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j)
    (hvis' : ∀ y ∈ chartAlgInf R F j, ∃ s ∈ chartAlgInf R F j',
      (∃ a ∈ chartAlgInf R F j', s = 1 + j'⁻¹ * a) ∧ s * y ∈ chartAlgInf R F j') :
    ∃ (w : AlgebraicCurve.TwoChartIntegralModel R F j ≅ AlgebraicCurve.TwoChartIntegralModel R F j')
      (ιF : chartAlgFin R F j' →ₐ[R] chartAlgFin R F j)
      (s : chartAlgInf R F j) (ψ : chartAlgInf R F j' →ₐ[R] Localization.Away s),
      (∀ x, (ιF x : F) = x) ∧ Function.Bijective ιF ∧
      (∃ a : chartAlgInf R F j, s = 1 + jInvChartInf R F j * a) ∧
      (∀ y : chartAlgInf R F j', ∃ (n : ℕ) (z : chartAlgInf R F j), (s : F) ^ n * (y : F) = z ∧
        ψ y * algebraMap _ (Localization.Away s) (s ^ n) = algebraMap _ (Localization.Away s) z) ∧
      w.hom ≫ toBase R F j' = toBase R F j ∧
      ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F j' ∧
      Spec.map (CommRingCat.ofHom (algebraMap (chartAlgInf R F j) (Localization.Away s))) ≫ ιInf R F j ≫ w.hom =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ιInf R F j' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_mem_chartAlgFin_of_forall_exists_mul_mem.solution
