import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_HeightOneSpectrum_adicCompletion_baseChangeAlgEquiv_congr_apply_eq_transport

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct NumberField.PlaceTransport
theorem HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv_congr_apply_eq_transport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (w w' : v.Extension (𝓞 L)) (h : σ • w.1 = w'.1)
    (y : L ⊗[K] v.adicCompletion K) :
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K) y) w' =
      NumberField.PlaceTransport.transport σ h
        (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w) := by p2m_exact_reverting @_root_.P2MW.S_HeightOneSpectrum_adicCompletion_baseChangeAlgEquiv_congr_apply_eq_transport.solution
