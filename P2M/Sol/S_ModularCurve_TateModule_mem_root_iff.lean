import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
namespace P2MW.S_ModularCurve_TateModule_mem_root_iff

set_option autoImplicit false

namespace TMIdentSol

theorem mem_iff (p : ℕ) (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlg J]
    (x : ℕ → J) :
    x ∈ _root_.TateModule p J ↔ x ∈ ModularCurve.TateModule p J := by
  constructor
  · intro hx
    refine ⟨?_, fun n => ?_⟩
    · have h := (hx 0).1
      simpa using h
    · have h := (hx n).2
      rwa [natCast_zsmul] at h
  · intro hx n
    refine ⟨?_, ?_⟩
    · rw [natCast_zsmul]
      exact ModularCurve.TateModule.pow_smul_apply hx n
    · rw [natCast_zsmul]
      exact hx.2 n

def equivRoot (p : ℕ) (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlg J] :
    ModularCurve.TateModule p J ≃+ _root_.TateModule p J where
  toFun x := ⟨x.1, (mem_iff p J x.1).mpr x.2⟩
  invFun y := ⟨y.1, (mem_iff p J y.1).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem equivRoot_hecke_smul (p : ℕ) (J : Type) [AddCommGroup J]
    [Module ModularCurve.HeckeAlg J] [Fact p.Prime] (t : ModularCurve.HeckeAlg)
    (x : ModularCurve.TateModule p J) :
    equivRoot p J (t • x)
      = _root_.TateModule.rep p J ModularCurve.HeckeAlg t (equivRoot p J x) :=
  Subtype.ext (funext fun _ => rfl)

theorem equivRoot_group_smul (p : ℕ) (J : Type) [AddCommGroup J]
    [Module ModularCurve.HeckeAlg J] [Fact p.Prime] {G : Type} [Group G]
    [DistribMulAction G J] [SMulCommClass G ModularCurve.HeckeAlg J] (g : G) {x : ℕ → J}
    (hx : x ∈ ModularCurve.TateModule p J) :
    equivRoot p J ⟨g • x, ModularCurve.TateModule.smul_mem g hx⟩
      = _root_.TateModule.rep p J G g (equivRoot p J ⟨x, hx⟩) :=
  Subtype.ext (funext fun _ => rfl)

end TMIdentSol

theorem solution (p : ℕ) (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlg J]
    (x : ℕ → J) :
    x ∈ TateModule p J ↔ x ∈ ModularCurve.TateModule p J :=
  TMIdentSol.mem_iff p J x
