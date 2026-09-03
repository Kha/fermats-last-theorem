import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal

open CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    {A : Type} [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ ModularCurve.IgusaScheme N ℓ) :
    (∃ α : ↥(chartAlgFin N ℓ) →+* A,
        f = Spec.map (CommRingCat.ofHom α) ≫ ModularCurve.IgusaScheme.ιFin N ℓ) ∨
      (∃ α : ↥(chartAlgInf N ℓ) →+* A,
        f = Spec.map (CommRingCat.ofHom α) ≫ ModularCurve.IgusaScheme.ιInf N ℓ ∧
          α (ModularCurve.IgusaScheme.jInvChartInf N ℓ) ∈ IsLocalRing.maximalIdeal A) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal.solution
