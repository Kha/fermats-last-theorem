import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Mathlib.Topology.Algebra.Support
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport

set_option autoImplicit false

open NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ U : Finset Kˣ, ∀ u : Kˣ, (u : K) ≠ 1 → u ∉ U →
      ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        f (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport.solution
