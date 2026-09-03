import Mathlib
import Definitions.Def_LocalGL2_Kirillov
import P2M.Util
import P2M.Sol.S_LocalGL2_Kirillov_exists_isBump

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LocalGL2.Kirillov.exists_isBump
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (hψ : ψ ≠ 1)
    (hψ0 : ∀ᶠ t in nhds (0 : v.adicCompletion K), ψ t = 1)
    (S : Submodule ℂ (GL (Fin 2) (v.adicCompletion K) → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (v.adicCompletion K), (fun g => W (g * k)) ∈ S)
    (hsm : ∀ W ∈ S, ∃ K₀ : Subgroup (GL (Fin 2) (v.adicCompletion K)),
      IsOpen (K₀ : Set (GL (Fin 2) (v.adicCompletion K))) ∧ ∀ k ∈ K₀, (fun g => W (g * k)) = W)
    (ϖ : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (δ : (WithZero (Multiplicative ℤ))ˣ) (n : ℤ) (τ : LocalGL2.Kirillov.Ch v δ)
    (ξ : (GL (Fin 2) (v.adicCompletion K) → ℂ) ⧸ LocalGL2.Kirillov.defectSpan v ψ S)
    (hξ : ξ ∈ LocalGL2.Kirillov.coinv v ψ S) :
    ∃ E ∈ S, LocalGL2.Kirillov.IsBump v ψ S ϖ n τ ξ E := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_Kirillov_exists_isBump.solution
