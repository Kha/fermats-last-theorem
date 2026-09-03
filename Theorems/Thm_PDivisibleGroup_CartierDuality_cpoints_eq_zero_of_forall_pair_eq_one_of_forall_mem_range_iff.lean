import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_CompletedPoints
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff
attribute [-instance] PrimaryTorsion.instSMul PrimaryTorsion.instModule PadicComplex.smulCommClass_gal_padic PadicComplex.smulCommClass_padic_gal PadicComplex.uniformContinuousConstSMul_gal PadicComplex.mulSemiringAction
attribute [-simp] PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul PadicComplex.galAlgHom_apply PadicComplex.smul_algebraMap PadicComplex.norm_smul_eq PadicComplex.nnnorm_smul_eq PadicComplex.smul_coe

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hR : ∀ x : PadicAlgCl p, x ∈ Set.range (algebraMap R (PadicAlgCl p)) ↔ x ∈ K ∧ ‖x‖ ≤ 1)
    (hinj : Function.Injective (algebraMap R (PadicAlgCl p)))
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (g : G.CPoints R)
    (hg : ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
      ∀ (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
          Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i}) w),
        G.pointsMkAdd _ w (Additive.ofMul f) =
          G.cpointsProj (integralClosure R (PadicAlgCl p)) i
            (G.cpointsMap (Algebra.ofId R (integralClosure R (PadicAlgCl p))) g) →
      ∀ (ψ : G'.Point (integralClosure R (PadicAlgCl p)) w),
        G'.pointsMkAdd (PadicAlgCl p) w
            (Additive.ofMul (G'.pointMap (integralClosure R (PadicAlgCl p)).val w ψ)) =
          (y : ℕ → G'.Points (PadicAlgCl p)) w →
        D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R
            (Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i})) w ψ) = 1) :
    g = 0 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff.solution
