import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd
open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem ModularCurve.exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (hqn : q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12)
    (𝒥 : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
    (M0int H1K M0loc H1Kloc : ℕ → Type)
    [∀ m, AddCommGroup (M0int m)] [∀ m, AddCommGroup (H1K m)]
    [∀ m, AddCommGroup (M0loc m)] [∀ m, AddCommGroup (H1Kloc m)]
    [∀ m, Module HeckeAlg (M0int m)] [∀ m, Module HeckeAlg (H1K m)]
    [∀ m, Module HeckeAlg (M0loc m)] [∀ m, Module HeckeAlg (H1Kloc m)]
    (δ : ∀ m, M0int m →ₗ[HeckeAlg] H1K m)
    (hδ : ∀ m, LinearMap.ker (δ m)
      = LinearMap.range ((q ^ m : HeckeAlg) • (LinearMap.id : M0int m →ₗ[HeckeAlg] M0int m)))
    (hH1K : ∀ m, ∀ x : H1K m, (q ^ m : HeckeAlg) • x = 0)
    (ℓ0 : ∀ m, M0int m →ₗ[HeckeAlg] M0loc m)
    [∀ m, IsLocalizedModule (eisensteinMaximalIdeal p q).primeCompl (ℓ0 m)]
    (ℓ1 : ∀ m, H1K m →ₗ[HeckeAlg] H1Kloc m)
    [∀ m, IsLocalizedModule (eisensteinMaximalIdeal p q).primeCompl (ℓ1 m)]
    (eH1 : ∀ m, H1Kloc m ≃+ fppfCohomology specInt (𝒥 m) 1)
    (M : Type) [AddCommGroup M] (toM : ∀ m, M0loc m →+ M)
    (htoM : ∀ m, Function.Injective (toM m)) (hfin : ∀ m, (toM m).range.FiniteIndex) :
    ∃ row : ∀ m, JKummerRow q m M,
      ∀ m, Nonempty (letI := (row m).instH1Jtors; (row m).H1Jtors ≃+ fppfCohomology specInt (𝒥 m) 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_jKummerRow_addEquiv_fppfCohomology_of_localizedKummerData_of_dvd.solution
