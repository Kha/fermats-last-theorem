import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero

set_option autoImplicit false

universe u

theorem Algebra.exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (t : R) (ht : (Ideal.span ({t} : Set R)).IsPrime) [CharZero (R ⧸ Ideal.span ({t} : Set R))]
    (𝔔 : Ideal S) [𝔔.IsPrime] (h𝔔 : 𝔔.height = 1) (ht𝔔 : algebraMap R S t ∈ 𝔔) :
    ∃ s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F)), ∃ u ∉ 𝔔, ∃ z ∈ 𝔔, u * algebraMap R S t = s * z := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_mem_comap_one_div_traceDual_mul_eq_mul_of_height_eq_one_of_charZero.solution
