import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import P2M.Util
namespace P2MW.S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Topology

theorem solution (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c ∧ 0 < d₁ ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∈ 𝓝 g := by
  classical
  refine ⟨1 / 2, 1, 1 / 2, 2, {g}, by norm_num, by norm_num, ?_⟩
  have h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ interior (centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2) :=
    one_mem_interior_centreCutSiegelSet (by norm_num) one_ne_zero (by norm_num) (by norm_num)
  have hW : (⋃ x ∈ ({g} : Finset (AdelicGL2 (𝓞 F) F)), (· * x) '' centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2) =
      (· * g) '' centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2 := by
    ext h
    simp only [Finset.mem_singleton, Set.mem_iUnion, exists_prop, exists_eq_left]
  rw [hW]
  have hn : centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2 ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F) := mem_interior_iff_mem_nhds.mp h1
  have him := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hn
  rw [Homeomorph.coe_mulRight] at him
  simpa only [one_mul] using him
