import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_resHom_artinFrob_eq_artinFrob_pow_inertiaDeg

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.resHom_artinFrob_eq_artinFrob_pow_inertiaDeg
    (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
    [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
    [IsMulCommutative (M ≃ₐ[K] M)]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hunr : ∀ Q : Ideal (𝓞 M), Q.IsMaximal → Q.under (𝓞 K) = v.asIdeal → Q.inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (artinFrob E N w) = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_resHom_artinFrob_eq_artinFrob_pow_inertiaDeg.solution
