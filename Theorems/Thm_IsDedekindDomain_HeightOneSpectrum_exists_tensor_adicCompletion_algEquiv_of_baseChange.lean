import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_tensor_adicCompletion_algEquiv_of_baseChange

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem IsDedekindDomain.HeightOneSpectrum.exists_tensor_adicCompletion_algEquiv_of_baseChange
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M]
    (hdisj : Module.finrank K' M = Module.finrank K L)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L)) (𝔳 : v.Extension (𝓞 K'))
    (hfin : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L) :
    ∃ e : (M ⊗[K'] 𝔳.1.adicCompletion K') ≃ₐ[𝔳.1.adicCompletion K']
        (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L),
      ∀ (a : K') (b : L) (c : 𝔳.1.adicCompletion K'),
        e ((algebraMap K' M a * algebraMap L M b) ⊗ₜ[K'] c) =
          (algebraMap K' (𝔳.1.adicCompletion K') a * c) ⊗ₜ[v.adicCompletion K]
            algebraMap L (w.1.adicCompletion L) b := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_tensor_adicCompletion_algEquiv_of_baseChange.solution
