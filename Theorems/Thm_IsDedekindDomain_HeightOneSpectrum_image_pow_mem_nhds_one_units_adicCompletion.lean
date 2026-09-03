import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.image_pow_mem_nhds_one_units_adicCompletion
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n)
    (V : Set (v.adicCompletion K)ˣ) (hV : V ∈ nhds (1 : (v.adicCompletion K)ˣ)) :
    (fun s : (v.adicCompletion K)ˣ => s ^ n) '' V ∈ nhds (1 : (v.adicCompletion K)ˣ) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion.solution
