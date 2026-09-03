import Definitions.Def_CerednikDrinfeld_MumfordGlue
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_of_affineNbhd_zero

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlue.affineNbhd_of_affineNbhd_zero
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    (h0 : ∀ S : Set (Gl.Z 0), S.Finite → ∃ U : (Gl.Z 0).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z 0))) :
    ∀ (n : ℕ) (S : Set (Gl.Z n)), S.Finite → ∃ U : (Gl.Z n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z n)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_of_affineNbhd_zero.solution
