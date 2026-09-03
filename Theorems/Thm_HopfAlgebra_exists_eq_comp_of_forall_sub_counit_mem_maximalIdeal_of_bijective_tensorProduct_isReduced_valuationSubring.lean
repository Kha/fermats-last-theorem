import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring
    (p : ℕ) [Fact p.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) [HenselianLocalRing P]
    (hp : (p : P) ∈ IsLocalRing.maximalIdeal P)
    (A : Type) [CommRing A] [HopfAlgebra P A] [Coalgebra.IsCocomm P A]
    [Module.Finite P A] [Module.Free P A]
    (hA : ∃ n : ℕ, Module.finrank P A = p ^ n)

    (M : Type) [CommRing M] [HopfAlgebra P M] [Coalgebra.IsCocomm P M] [Module.Free P M] [Module.Finite P M]
    (π : A →ₐc[P] M) (hπ : Function.Surjective π) (hMet : Algebra.Etale P (CartierDual P M))
    (hμbc : (∀ (R' : Type) [CommRing R'] [HenselianLocalRing R'] [Algebra P R'],
          IsLocalHom (algebraMap P R') →
          Algebra.Etale R' (CartierDual R' (R' ⊗[P] M)) ∧
          ∀ (N : Type) [CommRing N] [HopfAlgebra R' N] [Coalgebra.IsCocomm R' N]
            [Module.Free R' N] [Module.Finite R' N] [Algebra.Etale R' (CartierDual R' N)]
            (f : R' ⊗[P] A →ₐc[R'] N),
              ∃! g : R' ⊗[P] M →ₐc[R'] N,
                g.comp (Bialgebra.TensorProduct.map (BialgHom.id R' R') π) = f))

    (hord : ∃ (M₀ : Type) (_ : CommRing M₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) M₀)
        (_ : Module.Finite (IsLocalRing.ResidueField P) M₀) (_ : Module.Free (IsLocalRing.ResidueField P) M₀)
        (E₀ : Type) (_ : CommRing E₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) E₀)
        (Θ : IsLocalRing.ResidueField P ⊗[P] A →ₐc[IsLocalRing.ResidueField P]
          M₀ ⊗[IsLocalRing.ResidueField P] E₀),
        Function.Bijective Θ ∧ IsReduced E₀ ∧ IsReduced (CartierDual (IsLocalRing.ResidueField P) M₀))
    (f : A →ₐ[P] P) (hf : ∀ a : A, f a - Coalgebra.counit (R := P) a ∈ IsLocalRing.maximalIdeal P) :
    ∃ g : M →ₐ[P] P, f = g.comp (π : A →ₐ[P] M) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring.solution
