import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_prod_forall_act_eq_ed2

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_prod_forall_act_eq_ed2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    ∃ (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (B : FiniteAdeleRing (𝓞 L) L ≃+* FiniteAdeleRing (𝓞 L) L),
      Continuous A ∧ Continuous A.symm ∧ Continuous B ∧ Continuous B.symm ∧
      ∀ x : AdeleRing (𝓞 L) L, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) x = (A x.1, B x.2) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_prod_forall_act_eq_ed2.solution
