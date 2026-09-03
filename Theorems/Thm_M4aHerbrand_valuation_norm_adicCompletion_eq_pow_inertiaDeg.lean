import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (y : w.1.adicCompletion L) :
    Valued.v (Algebra.norm (v.adicCompletion K) y) =
      Valued.v y ^ Ideal.inertiaDeg' v.asIdeal w.1.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg.solution
