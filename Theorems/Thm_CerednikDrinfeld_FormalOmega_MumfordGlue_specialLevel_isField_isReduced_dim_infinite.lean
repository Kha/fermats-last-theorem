import Definitions.Def_CerednikDrinfeld_MumfordGlue
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_MumfordGlue_specialLevel_isField_isReduced_dim_infinite

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlue.specialLevel_isField_isReduced_dim_infinite
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    :
    IsField (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) ∧ IsReduced (Gl.Z 0) ∧
    (∀ z : Gl.Z 0, IsClosed ({z} : Set (Gl.Z 0)) ∨ closure ({z} : Set (Gl.Z 0)) ∈ irreducibleComponents (Gl.Z 0)) ∧
    (∀ C ∈ irreducibleComponents (Gl.Z 0), Set.Infinite C) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_specialLevel_isField_isReduced_dim_infinite.solution
