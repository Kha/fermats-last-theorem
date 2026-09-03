import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_exists_pow_smul_eq_of_forall_mem_zpowers

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField.PlaceTransport
theorem NumberField.PlaceTransport.exists_pow_smul_eq_of_forall_mem_zpowers
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (w w' : v.Extension (𝓞 L)) :
    ∃ n : ℕ, (σ ^ n) • w.1 = w'.1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_exists_pow_smul_eq_of_forall_mem_zpowers.solution
