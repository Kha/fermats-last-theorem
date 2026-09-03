import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import P2M.Util
import P2M.Sol.S_NumberField_raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin
open scoped IsMulCommutative nonZeroDivisors

universe u v

theorem NumberField.raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)]
    (n : ℕ) (ζ : M) (hζ : ζ ^ n = 1) (α : 𝓞 K) (hα : α ≠ 0)
    (hcop : ∀ v : HeightOneSpectrum (𝓞 K), α ∈ v.asIdeal → (n : 𝓞 K) ∉ v.asIdeal) :
    raySymbol K (artinFrob K M) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) ζ
      = ζ ^ Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_raySymbol_artinFrob_apply_eq_pow_absNorm_of_pow_eq_one.solution
