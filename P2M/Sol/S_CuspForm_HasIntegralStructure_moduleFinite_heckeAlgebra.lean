import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_intLattice_fg
import Theorems.Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra
import Theorems.Thm_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice
import P2M.Util
namespace P2MW.S_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra

noncomputable section

open ModularForm ModularFormClass

p2m_open "CuspForm ModularForm.CuspForm"

theorem solution {N : ℕ} [NeZero N] {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) (S : Set ℕ) : Module.Finite ℤ (CuspForm.heckeAlgebra N k S) := by
  classical
  let V := CuspForm (CongruenceSubgroup.Gamma0 N) k
  let L : Submodule ℤ V := intLattice N k
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr (CuspForm.intLattice_fg N k)
  haveI hVtf : IsAddTorsionFree V := by
    refine ⟨fun n hn a b hab => ?_⟩
    have h : (n : ℂ) • a = (n : ℂ) • b := by
      simpa only [Nat.cast_smul_eq_nsmul] using hab
    exact smul_right_injective V (Nat.cast_ne_zero.mpr hn) h
  haveI : IsAddTorsionFree L := by
    refine ⟨fun n hn a b hab => ?_⟩
    apply Subtype.ext
    apply IsAddTorsionFree.nsmul_right_injective hn
    have := congrArg Subtype.val hab
    simpa using this
  haveI : Module.Free ℤ L := inferInstance

  let ψ : heckeAlgebra N k S →ₗ[ℤ] Module.End ℤ L :=
    { toFun := fun t => ((t : Module.End ℂ V).restrictScalars ℤ).restrict
        (fun f hf => CuspForm.mem_intLattice_of_mem_heckeAlgebra hk t.2 hf)
      map_add' := fun t t' => by ext f; rfl
      map_smul' := fun n t => by
        ext f
        rfl }
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    apply Subtype.ext
    refine CuspForm.HasIntegralStructure.eq_zero_of_forall_mem_intLattice hN (t : Module.End ℂ V) fun f hf => ?_
    calc (t : Module.End ℂ V) f = ((ψ t ⟨f, hf⟩ : L) : V) := rfl
      _ = 0 := by rw [ht]; rfl
  exact Module.Finite.of_injective ψ hψ

end
