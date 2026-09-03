import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_IntegralClosure_exists_extend_ringHom_dvr_finite

set_option autoImplicit false

theorem IntegralClosure.exists_extend_ringHom_dvr_finite
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')]
    [CharZero 𝒪'] {p : ℕ} (hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪')
    (R : Subalgebra ℤ (integralClosure ℤ ℂ)) (s : Finset (integralClosure ℤ ℂ))
    (φ : R →+* 𝒪') :
    ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪'') 𝒪'')
      (_ : Finite (IsLocalRing.ResidueField 𝒪'')) (_ : CharZero 𝒪'')
      (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'') (_ : IsLocalHom (algebraMap 𝒪' 𝒪'')),
      (p : 𝒪'') ∈ IsLocalRing.maximalIdeal 𝒪'' ∧
      Function.Injective (algebraMap 𝒪' 𝒪'') ∧
      ∃ φ' : ↥(R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ))) →+* 𝒪'',
        ∀ x : R, φ' (Subalgebra.inclusion le_sup_left x) = algebraMap 𝒪' 𝒪'' (φ x) := by p2m_exact_reverting @_root_.P2MW.S_IntegralClosure_exists_extend_ringHom_dvr_finite.solution
