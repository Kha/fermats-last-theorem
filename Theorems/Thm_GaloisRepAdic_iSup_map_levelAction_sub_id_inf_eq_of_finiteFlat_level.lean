import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level
attribute [-instance] instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

open IsLocalRing

theorem GaloisRepAdic.iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpA : (p : A) ∈ maximalIdeal A)
    (I : Ideal A) [Finite (A ⧸ I)]
    (hfl : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))),
        (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.levelAction I σ (e f))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (N : Submodule A (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))))
    (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, N.map (ρ.levelAction I σ) ≤ N) :
    (⨆ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρ.levelAction I σ - LinearMap.id)) ⊓ N =
      ⨆ σ ∈ P.inertiaSubgroupIn ℚ, N.map (ρ.levelAction I σ - LinearMap.id) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level.solution
