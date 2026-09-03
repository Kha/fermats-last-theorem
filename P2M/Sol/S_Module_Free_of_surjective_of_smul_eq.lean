import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Module.Torsion.Basic
import P2M.Util
namespace P2MW.S_Module_Free_of_surjective_of_smul_eq

theorem FrobChareqDock.bijective_aux {S T N : Type*} [CommRing S] [Ring T]
    [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] [Nontrivial N]
    (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) :
    Function.Bijective g := by
  refine ⟨?_, hsurj⟩
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro s hs
  have hann : s ∈ Module.annihilator S N := Module.mem_annihilator.mpr fun n => by
    rw [← hg s n, RingHom.mem_ker.mp hs, zero_smul]
  rwa [(Module.annihilator_eq_bot (R := S) (M := N)).mpr inferInstance] at hann

theorem solution {S T N : Type*} [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) : Module.Free T N := by
  rcases subsingleton_or_nontrivial N with _ | _
  · infer_instance
  · exact Module.Free.of_basis <| (Module.Free.chooseBasis S N).mapCoeffs
      (RingEquiv.ofBijective g (FrobChareqDock.bijective_aux g hg hsurj)) (fun c x => hg c x)
