import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual

set_option autoImplicit false

universe u

theorem Algebra.exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (I : Ideal R) (s : S)
    (hs : s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))) :
    ∀ φ : Module.Dual (R ⧸ I) (S ⧸ I.map (algebraMap R S)),
      ∃ x : S ⧸ I.map (algebraMap R S), ∀ y : S ⧸ I.map (algebraMap R S),
        φ (Ideal.Quotient.mk (I.map (algebraMap R S)) s * y) =
          Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (x * y) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual.solution
