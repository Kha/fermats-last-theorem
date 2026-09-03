import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_mk_mem_pow_ramificationIdx_sub_one_of_mem_comap_one_div_traceDual

set_option autoImplicit false

universe u

open IsLocalRing

theorem Algebra.mk_mem_pow_ramificationIdx_sub_one_of_mem_comap_one_div_traceDual
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (ϖ : R) (hϖ0 : ϖ ≠ 0) [hϖp : (Ideal.span ({ϖ} : Set R)).IsPrime] (hϖ : IsDiscreteValuationRing (R ⧸ Ideal.span ({ϖ} : Set R)))
    (hfib : IsDedekindDomain (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S)))
    (hunr : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], algebraMap R S ϖ ∈ 𝔔 → 𝔔.height = 1 → Algebra.IsUnramifiedAt R 𝔔)
    (s : S) (hs : s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F)))
    (x : Ideal (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) [x.IsMaximal]
    (n : ℕ) (hn : ((maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span ({ϖ} : Set R)))).map
      (algebraMap (R ⧸ Ideal.span ({ϖ} : Set R)) (S ⧸ (Ideal.span ({ϖ} : Set R)).map (algebraMap R S))) ≤ x ^ n) :
    Ideal.Quotient.mk ((Ideal.span ({ϖ} : Set R)).map (algebraMap R S)) s ∈ x ^ (n - 1) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_mk_mem_pow_ramificationIdx_sub_one_of_mem_comap_one_div_traceDual.solution
