import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_ModularCurve_forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap

set_option autoImplicit false
open scoped MatrixGroups TensorProduct
open IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel

theorem ModularCurve.forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)

    (B : Subalgebra (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hlift : ∀ b : ↥B, ∃ y : LaurentSeries (R p),
      coeffMap (algebraMap (R p) ℚ) y = (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))

    (r₀ : ↥B →+* ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM)))
    (hr₀ : ∀ (b : ↥B) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) →
      ((r₀ b : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)) =
        coeffMap ((residue ↥Pl).comp ρ) y)

    (Rg : RegularProlongation Pl ↥(xHFunctionFieldBar M H) ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H)))
    (hq : ∀ (y : LaurentSeries ↥Pl) (hy : coeffMap Pl.subtype y ∈ xHFunctionFieldBar M H),
      ∃ hO : (⟨coeffMap Pl.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
        ((Rg.residue ⟨_, hO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H))) : LaurentSeries (ResidueField ↥Pl)) =
          coeffMap (residue ↥Pl) y)

    (γ : ↥Pl ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (α : ↥Pl) (b : ↥B), ((γ (α ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (α : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (r : ↥Pl ⊗[R p] ↥B →+* ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM)))
    (hr : ∀ (α : ↥Pl) (b : ↥B), ((r (α ⊗ₜ b) : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)) =
      residue ↥Pl α • ((r₀ b : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)))
    (t : ↥Pl ⊗[R p] ↥B) :
    ∃ hO : γ t ∈ Rg.integers,
      ((Rg.residue ⟨γ t, hO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓM M H))) : LaurentSeries (ResidueField ↥Pl)) =
        ((r t : ↥(qExpFunctionFieldC (ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥Pl)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_forall_mem_integers_and_coe_residue_eq_of_tmul_of_forall_coe_eq_coeffMap.solution
