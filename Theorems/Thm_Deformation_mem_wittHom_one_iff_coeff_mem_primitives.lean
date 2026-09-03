import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
import P2M.Sol.S_Deformation_mem_wittHom_one_iff_coeff_mem_primitives

universe u v

theorem Deformation.mem_wittHom_one_iff_coeff_mem_primitives
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] (x : TruncatedWittVector p 1 A) :
    x ∈ Deformation.wittHom k p 1 A ↔ x.coeff 0 ∈ primitives k A := by p2m_exact_reverting @_root_.P2MW.S_Deformation_mem_wittHom_one_iff_coeff_mem_primitives.solution
