import Mathlib
import P2M.Util
import P2M.Sol.S_UniqueFactorizationMonoid_dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt

set_option autoImplicit false

open IsLocalRing Polynomial

theorem UniqueFactorizationMonoid.dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (p : R) (hp : Prime p) (e : ℕ) (he : 0 < e) (f : R) (hf : f ≠ 0)
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    (α : F) (hα : α ^ e = algebraMap R F f)
    (hunr : ∀ (𝔓 : Ideal B) [𝔓.IsPrime], 𝔓.comap (algebraMap R B) = Ideal.span {p} → Algebra.IsUnramifiedAt R 𝔓) :
    e ∣ multiplicity p f := by p2m_exact_reverting @_root_.P2MW.S_UniqueFactorizationMonoid_dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt.solution
