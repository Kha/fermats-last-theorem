import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_finrank_le_of_forall_point_exists_extension

set_option autoImplicit false

open IsLocalRing

theorem CuspForm.heckeLocal.finrank_le_of_forall_point_exists_extension
    (N : ℕ) [NeZero N] (S S₀ : Set ℕ) (hS₀ : S₀ ⊆ S)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra N 2 S₀ →+* ResidueField 𝒪)
    (hlift : ∀ (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
        [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
        [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')],
        Function.Injective (algebraMap 𝒪 𝒪') →
      ∀ χ : CuspForm.heckeAlgebra N 2 S →+* 𝒪',
        (∀ t, residue 𝒪' (χ t) = ResidueField.map (algebraMap 𝒪 𝒪') (θ t)) →
        ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
          (_ : IsAdicComplete (maximalIdeal 𝒪'') 𝒪'') (_ : Finite (ResidueField 𝒪''))
          (_ : CharZero 𝒪'') (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'')
          (_ : IsLocalHom (algebraMap 𝒪' 𝒪'')),
        Function.Injective (algebraMap 𝒪' 𝒪'') ∧
        ∃ χ' : CuspForm.heckeAlgebra N 2 S₀ →+* 𝒪'',
          (∀ t : CuspForm.heckeAlgebra N 2 S,
            χ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS₀) t) =
              algebraMap 𝒪' 𝒪'' (χ t)) ∧
          ∀ t : CuspForm.heckeAlgebra N 2 S₀, residue 𝒪'' (χ' t) =
            ResidueField.map (algebraMap 𝒪' 𝒪'') (ResidueField.map (algebraMap 𝒪 𝒪') (θ' t))) :
    Module.finrank 𝒪 (CuspForm.heckeLocal N S 𝒪 θ) ≤
      Module.finrank 𝒪 (CuspForm.heckeLocal N S₀ 𝒪 θ') := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_finrank_le_of_forall_point_exists_extension.solution
