import Decoupling.HighDim.StableFreeEffectiveCochainFrame
import Decoupling.HighDim.AlgorithmTwoFiniteComplexBasis
import Mathlib.Data.List.Nodup

/-!
# Original per-degree coordinates from an explicit total grade array

The selected basis is the increasing filtered list of existing total
indices. No field-basis choice occurs. The lookup vectors are computable;
their native linear equivalences are semantic proofs of that same ordering.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory AlgorithmTwoFiniteComplex StableFree.Effective.CochainProgram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {N : ℕ}

def gradeIndices (degree : Vector ℤ N) (j : ℤ) : List (Fin N) :=
  (List.finRange N).filter (fun i => degree.get i = j)

def gradeRank (degree : Vector ℤ N) (j : ℤ) : ℕ := (gradeIndices degree j).length

def gradeSelector (degree : Vector ℤ N) (j : ℤ) : Vector (Fin N) (gradeRank degree j) :=
  Vector.ofFn fun i => (gradeIndices degree j).get i

theorem gradeSelector_get (degree : Vector ℤ N) (j : ℤ) (i : Fin (gradeRank degree j)) :
    (gradeSelector degree j).get i = (gradeIndices degree j).get i := by
  change (Vector.ofFn _)[i.val] = _
  rw [Vector.getElem_ofFn]

theorem gradeIndices_mem (degree : Vector ℤ N) (j : ℤ) (i : Fin N) :
    i ∈ gradeIndices degree j ↔ degree.get i = j := by simp [gradeIndices]

theorem gradeIndices_nodup (degree : Vector ℤ N) (j : ℤ) : (gradeIndices degree j).Nodup :=
  (List.nodup_finRange N).filter _

theorem gradeSelector_degree (degree : Vector ℤ N) (j : ℤ) (i : Fin (gradeRank degree j)) :
    degree.get ((gradeSelector degree j).get i) = j := by
  rw [gradeSelector_get]
  exact (gradeIndices_mem degree j _).mp (List.get_mem _ _)

theorem gradeSelector_injective (degree : Vector ℤ N) (j : ℤ) :
    Function.Injective (gradeSelector degree j).get := by
  intro i k he
  rw [gradeSelector_get,gradeSelector_get] at he
  exact (gradeIndices_nodup degree j).get_inj_iff.mp he

theorem gradeRank_le (degree : Vector ℤ N) (j : ℤ) : gradeRank degree j ≤ N := by
  simpa only [gradeRank,gradeIndices,List.length_finRange] using
    List.length_filter_le (fun i => degree.get i = j) (List.finRange N)

def selectorsFromDegree (degree : Vector ℤ N) : TermSelectors (gradeRank degree) N where
  atDegree := gradeSelector degree

noncomputable section
universe u
variable {R : Type u} [CommRing R] {C : CochainComplex (ModuleCat R) ℤ}

def gradeEquiv (degree : Vector ℤ N) (j : ℤ) : Fin (gradeRank degree j) ≃ Fiber degree j :=
  Equiv.ofBijective (fun i => ⟨(gradeSelector degree j).get i, gradeSelector_degree degree j i⟩) (by
    constructor
    · intro i k he
      exact gradeSelector_injective degree j (congrArg Subtype.val he)
    · intro i
      obtain ⟨k,hk⟩ := List.mem_iff_get.mp ((gradeIndices_mem degree j i.val).mpr i.property)
      exact ⟨k,Subtype.ext ((gradeSelector_get degree j k).trans hk)⟩)

def frameFiberEquiv (c : Coordinates C N) (j : ℤ) : C.X j ≃ₗ[R] (Fiber c.degree j → R) where
  toFun x i := c.embed j x i.val
  invFun y := c.project j (fiberEmbed c.degree j y)
  left_inv x := by
    have he : fiberEmbed c.degree j (fun i => c.embed j x i.val) = c.embed j x := by
      funext i
      change (if hi : c.degree.get i=j then c.embed j x i else 0) = _
      split_ifs with hi
      · rfl
      · exact (c.embed_supported j x i hi).symm
    change c.project j (fiberEmbed c.degree j (fun i => c.embed j x i.val)) = x
    rw [he,c.project_embed]
  right_inv y := by
    funext i
    change c.embed j (c.project j (fiberEmbed c.degree j y)) i.val = y i
    rw [c.embed_project,ite_eq_left i.property]
    change (if hi : c.degree.get i.val=j then y ⟨i.val,hi⟩ else 0) = y i
    rw [dite_eq_left i.property]
  map_add' x y := by funext i; exact congrFun ((c.embed j).map_add x y) i.val
  map_smul' a x := by funext i; exact congrFun ((c.embed j).map_smul a x) i.val

def originalFromFrame (c : Coordinates C N) : StableFree.Coordinates C where
  rank := gradeRank c.degree
  equiv j := (frameFiberEquiv c j).trans (LinearEquiv.funCongrLeft R R (gradeEquiv c.degree j))

theorem originalFromFrame_apply (c : Coordinates C N) (j : ℤ) (x : C.X j)
    (i : Fin (gradeRank c.degree j)) :
    (originalFromFrame c).equiv j x i = c.embed j x ((gradeSelector c.degree j).get i) := rfl

theorem selectorsFromDegree_realizes {K : Type u} [Field K] {D : ℕ}
    {C : CochainComplex (ModuleCat.{u} (Laurent K D)) ℤ} (c : Coordinates C N) :
    FrameRealizes (originalFromFrame c) c (selectorsFromDegree c.degree) := by
  constructor
  · intro j x i
    exact (originalFromFrame_apply c j x i).symm
  · intro j i
    let q := (gradeSelector c.degree j).get i
    have hq : c.degree.get q = j := gradeSelector_degree c.degree j i
    have he : (originalFromFrame c).equiv j (c.project j (Pi.single q 1)) = Pi.single i 1 := by
      funext k
      rw [originalFromFrame_apply, c.embed_project, ite_eq_left (gradeSelector_degree c.degree j k)]
      have hk : (gradeSelector c.degree j).get k = q ↔ k=i :=
        (gradeSelector_injective c.degree j).eq_iff
      simp only [Pi.single_apply, hk]
    have hx : ((originalFromFrame c).equiv j).symm (Pi.single i 1) = c.project j (Pi.single q 1) := by
      apply ((originalFromFrame c).equiv j).injective
      rw [LinearEquiv.apply_symm_apply,he]
    rw [hx]
    apply c.project_supported
    intro a ha
    have hne : a ≠ q := by intro h; subst a; exact ha hq
    simp [hne]

end
end Decoupling.HighDim.AlgorithmTwoPipeline
