import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero

set_option autoImplicit false

universe u

open IsLocalRing

theorem Algebra.map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (t : R) (ht : (Ideal.span ({t} : Set R)).IsPrime) [CharZero (R ⧸ Ideal.span ({t} : Set R))]
    (x : Ideal S) [x.IsPrime] [UniqueFactorizationMonoid (Localization.AtPrime x)]
    (hunr : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], 𝔔 ≤ x → 𝔔.height = 1 → algebraMap R S t ∉ 𝔔 → Algebra.IsUnramifiedAt R 𝔔) :
    Ideal.map (algebraMap S (Localization.AtPrime x)) (Ideal.span {algebraMap R S t}) ≤
      (Ideal.map (algebraMap S (Localization.AtPrime x)) (Ideal.span {algebraMap R S t})).radical *
        Ideal.map (algebraMap S (Localization.AtPrime x))
          (((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_map_span_le_radical_mul_map_comap_one_div_traceDual_of_isUnramifiedAt_of_charZero.solution
