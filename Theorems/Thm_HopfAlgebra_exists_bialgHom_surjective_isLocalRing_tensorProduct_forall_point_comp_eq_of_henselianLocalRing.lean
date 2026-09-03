import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing
attribute [-instance] HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient
attribute [-simp] HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing
    (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [HenselianLocalRing O]
    [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hloc : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O →
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal O)
    (C : Type) [CommRing C] [HopfAlgebra O C] [Coalgebra.IsCocomm O C]
    [Module.Finite O C] [Module.Free O C] :
    ∃ (C₀ : Type) (_ : CommRing C₀) (_ : HopfAlgebra O C₀) (_ : Coalgebra.IsCocomm O C₀)
      (_ : Module.Finite O C₀) (_ : Module.Free O C₀)
      (q₀ : C →ₐc[O] C₀),
      Function.Surjective q₀ ∧

      IsLocalRing (ZMod p ⊗[O] C₀) ∧

      (∀ f : C →ₐ[O] AlgebraicClosure ℚ,
        (∀ c : C, P.valuation (f c - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1) →
        ∃ g : C₀ →ₐ[O] AlgebraicClosure ℚ, f = g.comp (q₀ : C →ₐ[O] C₀)) ∧

      (∀ (L : Type) [CommRing L] [IsLocalRing L] [Algebra O L], IsLocalHom (algebraMap O L) →
        ∀ f : C →ₐ[O] L, (∀ c : C, f c - algebraMap O L (Coalgebra.counit c) ∈ IsLocalRing.maximalIdeal L) →
        ∃ g : C₀ →ₐ[O] L, f = g.comp (q₀ : C →ₐ[O] C₀)) ∧

      (∀ φ : C →ₐc[O] C, ∃! ψ : C₀ →ₐc[O] C₀, ψ.comp q₀ = q₀.comp φ) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing.solution
