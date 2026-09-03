import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
attribute [-instance] PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule
attribute [-simp] PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.CartierDuality.exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h} (D : G.CartierDuality G')
    {n : ℕ} (hn : G.HasDimension n) :
    ∃ φ : Fin n →
        (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p))) →ₗ[ℂ_[p]] ℂ_[p]),
      LinearIndependent ℂ_[p] φ ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
        (∀ x : PadicAlgCl p, τ x = σ x) → ∀ (j : Fin n)
        (x : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (G'.Points (PadicAlgCl p)))),
        φ j (TensorProduct.map (PadicComplex.galAlgHom p σ).toLinearMap
            ((G'.tateModuleRep (PadicAlgCl p) τ).baseChange ℚ_[p]) x) =
          σ • φ j x := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_exists_linearIndependent_invariant_dual_padicComplex_tateModule_of_hasDimension_of_ringOfIntegers.solution
