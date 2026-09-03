import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_CuspForm_HeckeGaloisRepDatum_exists_pi_eq_and_isFlatAt_of_comp_pi_eq
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

open Polynomial

theorem CuspForm.HeckeGaloisRepDatum.exists_pi_eq_and_isFlatAt_of_comp_pi_eq
    {N : ℕ} [NeZero N] {S : Finset ℕ}
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
    {T₀ : Type} [CommRing T₀] [IsLocalRing T₀] [IsNoetherianRing T₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal T₀) T₀] [Algebra 𝒪 T₀]
    [IsLocalHom (algebraMap 𝒪 T₀)] [Module.Finite 𝒪 T₀] [Module.Free 𝒪 T₀]
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T]
    [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H₀ : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T₀)
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T)
    (φ : T₀ →ₐ[𝒪] T) (hφ : IsLocalHom φ.toRingHom) (hfac : ∀ t, φ (H₀.π t) = H.π t)
    {p : ℕ} (hflat : H₀.ρ.IsFlatAt p) :
    ∃ H' : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T, H'.π = H.π ∧ H'.ρ.IsFlatAt p := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HeckeGaloisRepDatum_exists_pi_eq_and_isFlatAt_of_comp_pi_eq.solution
