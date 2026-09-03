import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.RingTheory.Norm.Basic
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_bijective_act_sub_algebraMap_mul_of_norm_ne_one

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.IdeleGaloisDescent.bijective_act_sub_algebraMap_mul_of_norm_ne_one
    {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
    (D : M4aHerbrand.IdeleGaloisDescent R E F)
    {σ : F ≃ₐ[E] F} (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ)
    (c : F) (hc : Algebra.norm E c ≠ 1) :
    Function.Bijective fun s : AdeleRing R F =>
      (D.act σ : RingAut (AdeleRing R F)) s - algebraMap F (AdeleRing R F) c * s := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_bijective_act_sub_algebraMap_mul_of_norm_ne_one.solution
