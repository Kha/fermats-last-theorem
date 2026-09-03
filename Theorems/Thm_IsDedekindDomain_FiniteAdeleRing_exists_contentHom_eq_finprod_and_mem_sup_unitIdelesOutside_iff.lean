import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff

set_option autoImplicit false
open IsDedekindDomain
open scoped nonZeroDivisors

theorem IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ φ : (FiniteAdeleRing R K)ˣ →* (FractionalIdeal R⁰ K)ˣ,
      (∀ x : (FiniteAdeleRing R K)ˣ, ((φ x : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
        ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (-(WithZero.log (Valued.v ((x : FiniteAdeleRing R K) v))))) ∧
      (∀ k : Kˣ, φ (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) k) = toPrincipalIdeal R K k) ∧
      Function.Surjective φ ∧
      φ.ker = IsDedekindDomain.FiniteAdeleRing.unitIdeles R K ∧
      (∀ (T : Set (HeightOneSpectrum R)) (x : (FiniteAdeleRing R K)ˣ),
        x ∈ (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range ⊔
            IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K T ↔
          ClassGroup.mk K (φ x) ∈ Subgroup.closure
            {c : ClassGroup R | ∃ v ∈ T, ∃ h : v.asIdeal ∈ (Ideal R)⁰, ClassGroup.mk0 ⟨v.asIdeal, h⟩ = c}) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.solution
