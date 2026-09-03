import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRLevel_mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss

set_option autoImplicit false

open scoped MatrixGroups TensorProduct
open IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y) :
    (∀ t : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj), γ t ∈ Rg.integers) ∧
    (∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      ∃ h : γ (a ⊗ₜ b) ∈ Rg.integers,
        ((Rg.residue ⟨γ (a ⊗ₜ b), h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
          IsLocalRing.residue ↥A a • coeffMap ((IsLocalRing.residue ↥A).comp ρ) y) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRLevel_mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss.solution
