import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isUnitFactorizableAt_rightConv_ne_zero
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_isUnitFactorizableAt_rightConv_ne_zero
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ)
    (v : HeightOneSpectrum (𝓞 K))
    (D E₀ : Ideal (𝓞 K)) (k : ℕ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ (D * E₀ * v.asIdeal ^ k) S π φ)
    (hφD : ∀ g : AdelicGL2 (𝓞 K) K,
      ∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
        φ (g * x) = φ g)
    (hφ0 : φ ≠ 0) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsUnitFactorizableAt K ⊥ S f ∧
      (∀ x ∈ levelOne (𝓞 K) K D ⊓ principalLevel (𝓞 K) K (E₀ * v.asIdeal ^ k) ⊓ finiteAdelicGL2Subgroup K,
        ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) ∧
      (∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
        f (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f y) ∧
      rightConv K φ f ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isUnitFactorizableAt_rightConv_ne_zero.solution
