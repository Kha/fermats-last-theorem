import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.XOneP.algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    [NeZero p]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hWσ : ∃ (ι : L →+* ℂ) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M ∧ (p : ℤ) ∣ γ 1 1 ∧
        ∀ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg → ModularCurve.intSeriesC ℚ pg ≠ 0 →
          ∀ x : ↥K, (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ∃ (φf φg : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
            (⇑φf : UpperHalfPlane → ℂ) = (Df : ℂ) • (fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (⇑φg : UpperHalfPlane → ℂ) = (Dg : ℂ) • (fun τ : UpperHalfPlane => ((⇑g : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι (c i)) • F i) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι (c i)) • F i) ∧
            ModularCurve.coeffMap ι ((σ x : ↥K) : LaurentSeries L) * HahnSeries.C (Df : ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φg : UpperHalfPlane → ℂ)) =
              HahnSeries.C (Dg : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φf : UpperHalfPlane → ℂ))) :
    (∀ (d d' : ℕ), d.Coprime (M * p) → d'.Coprime (M * p) →
        ((d' : ZMod M) = (d : ZMod M)) → ((d' : ZMod p) * (d : ZMod p) = 1) →
        ∀ (θd θd' : ↥K ≃ₐ[L] ↥K),
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θd x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θd' x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          ∀ x : ↥K, ((σ (θd (σ.symm x)) : ↥K) : LaurentSeries L) = ((θd' x : ↥K) : LaurentSeries L)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_algEquiv_diamond_symm_eq_diamond_of_generatorLaw_x1_mul.solution
