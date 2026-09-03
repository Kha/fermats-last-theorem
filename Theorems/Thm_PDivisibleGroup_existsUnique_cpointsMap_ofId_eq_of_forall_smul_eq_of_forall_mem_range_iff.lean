import Mathlib
import Definitions.Def_PDivisibleGroup_CompletedPoints
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff
attribute [-instance] PadicComplex.smulCommClass_gal_padic PadicComplex.smulCommClass_padic_gal PadicComplex.uniformContinuousConstSMul_gal PadicComplex.mulSemiringAction
attribute [-simp] PadicComplex.galAlgHom_apply PadicComplex.smul_algebraMap PadicComplex.norm_smul_eq PadicComplex.nnnorm_smul_eq PadicComplex.smul_coe

set_option autoImplicit false

theorem PDivisibleGroup.existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hR : ∀ x : PadicAlgCl p, x ∈ Set.range (algebraMap R (PadicAlgCl p)) ↔ x ∈ K ∧ ‖x‖ ≤ 1)
    (hinj : Function.Injective (algebraMap R (PadicAlgCl p)))
    {h : ℕ} (G : PDivisibleGroup R p h)
    (x : G.CPoints (integralClosure R (PadicAlgCl p)))
    (hx : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (σ' : integralClosure R (PadicAlgCl p) ≃ₐ[R] integralClosure R (PadicAlgCl p)),
      (∀ a : integralClosure R (PadicAlgCl p),
          ((σ' a : integralClosure R (PadicAlgCl p)) : PadicAlgCl p) = σ a) →
      σ' • x = x) :
    ∃! x₀ : G.CPoints R,
      G.cpointsMap (Algebra.ofId R (integralClosure R (PadicAlgCl p))) x₀ = x := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_existsUnique_cpointsMap_ofId_eq_of_forall_smul_eq_of_forall_mem_range_iff.solution
