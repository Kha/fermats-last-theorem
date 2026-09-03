import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.LocallyConstant.Basic
import P2M.Util
import P2M.Sol.S_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport

theorem IsLocallyConstant.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport.solution
