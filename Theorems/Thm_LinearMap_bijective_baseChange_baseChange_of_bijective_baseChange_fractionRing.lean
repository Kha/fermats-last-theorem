import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_bijective_baseChange_baseChange_of_bijective_baseChange_fractionRing

universe u v

theorem LinearMap.bijective_baseChange_baseChange_of_bijective_baseChange_fractionRing
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Bijective (f.baseChange K))
    (R₂ : Type u) [CommRing R₂] [IsDomain R₂] [Algebra R R₂] (hinj : Function.Injective (algebraMap R R₂))
    (K₂ : Type u) [Field K₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂] :
    Function.Bijective ((f.baseChange R₂).baseChange K₂) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_bijective_baseChange_baseChange_of_bijective_baseChange_fractionRing.solution
