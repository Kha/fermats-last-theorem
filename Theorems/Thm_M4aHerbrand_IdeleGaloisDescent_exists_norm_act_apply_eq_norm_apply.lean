import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_M4aHerbrand_IdeleGaloisDescent_exists_norm_act_apply_eq_norm_apply

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem M4aHerbrand.IdeleGaloisDescent.exists_norm_act_apply_eq_norm_apply
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    (∀ (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)), ∃ w' : v.Extension (𝓞 L),
        ‖((D.act σ : RingAut (AdeleRing (𝓞 L) L)) a).2 w.1‖ = ‖a.2 w'.1‖) ∧
    (∀ w : InfinitePlace L, ∃ w' : InfinitePlace L,
        ‖((D.act σ : RingAut (AdeleRing (𝓞 L) L)) a).1 w‖ = ‖a.1 w'‖) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_norm_act_apply_eq_norm_apply.solution
