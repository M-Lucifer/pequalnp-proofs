import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18828
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.HeptadCover

abbrev pt (i : Fin 13) : Fin 26 := Fin.castAdd 13 i
abbrev ln (i : Fin 13) : Fin 26 := Fin.natAdd 13 i
abbrev idx (v : Fin 26) := Fin.ofNat 13 v.val
def shift (v w : Fin 26) : Fin 26 :=
  if v.val < 13 then
    if w.val < 13 then pt (idx w - idx v) else ln (idx w - idx v)
  else
    if w.val < 13 then ln (idx v - idx w) else pt (idx v - idx w)

def adj (a b : Fin 26) : Prop := if a.val < 13 then
    13 ≤ b.val ∧ idx a ∈ singerLines3 (idx b)
  else b.val < 13 ∧ idx b ∈ singerLines3 (idx a)

abbrev F (x : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, p ∈ singerLines3 l ∧ x (pt p) = true ∧ x (ln l) = true

theorem toGraph (x : Fin 26 → Bool) : F x ↔ ∃ a b, adj a b ∧ x a = true ∧ x b = true := by
  have row : ∀ p l : Fin 13, adj (pt p) (ln l) ↔ p ∈ singerLines3 l := by unfold adj; decide +kernel
  have ends : ∀ a : Fin 26, (a.val < 13 → pt (idx a) = a) ∧ (13 ≤ a.val → ln (idx a) = a) := by decide +kernel
  constructor
  · rintro ⟨p,l,e,hp,hl⟩
    exact ⟨pt p,ln l,(row p l).mpr e,hp,hl⟩
  · rintro ⟨a,b,e,ha,hb⟩
    unfold adj at e
    split at e
    next low =>
      exact ⟨idx a,idx b,e.2,by rwa [(ends a).1 low],by rwa [(ends b).2 e.1]⟩
    next high =>
      exact ⟨idx b,idx a,e.2,by rwa [(ends b).1 e.1],by rwa [(ends a).2 (by omega)]⟩

set_option maxHeartbeats 4000000 in
theorem symmetry (v : Fin 26) : Function.Bijective (shift v) ∧ shift v v = 0 ∧ ∀ a b, adj (shift v a) (shift v b) ↔ adj a b := by
  have inj : ∀ v a b, shift v a = shift v b → a = b := by decide +kernel
  have zero : ∀ v, shift v v = 0 := by decide +kernel
  have symm : ∀ v a b, adj (shift v a) (shift v b) ↔ adj a b := by unfold adj; decide +kernel
  exact ⟨Finite.injective_iff_bijective.mp (fun _ _ h => inj v _ _ h), zero v, symm v⟩

theorem transport (v : Fin 26) (C : Circuit) (hC : IsAO2 26 C) :
    ∃ (σ : Fin 26 → Fin 26) (D : Circuit), Function.Bijective σ ∧ σ v = 0 ∧
      IsAO2 26 D ∧ D.size = C.size ∧
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ))) ∧
      ∀ x : Fin 26 → Bool, F (x ∘ σ) ↔ F x := by
  let wire (k : Fin 26) (i : ℕ) := if h : i < 26 then (shift k ⟨i, h⟩).val else i
  have wireBound (k : Fin 26) (i j : ℕ) (hi : i < 26 + j) : wire k i < 26 + j := by
    by_cases h : i < 26
    · exact (show wire k i < 26 by simp [wire, h]).trans_le (by omega)
    · simpa [wire, h] using hi
  let renameGate (k : Fin 26) (g : Gate) : Gate := ⟨g.op, g.inputs.map (wire k)⟩
  let D (k : Fin 26) : Circuit := ⟨C.gates.map (renameGate k), wire k C.output⟩
  have dSize (k : Fin 26) : (D k).size = C.size := by
    change (C.gates.map (renameGate k)).length = C.gates.length
    exact List.length_map _
  have dModel (k : Fin 26) : IsAO2 26 (D k) := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      change g ∈ C.gates.map (renameGate k) at hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact hC.1 g' hg'
    · intro j hj i hi
      change j < (C.gates.map (renameGate k)).length at hj
      simp only [List.length_map] at hj
      change i ∈ ((C.gates.map (renameGate k)).getD j ⟨.or, []⟩).inputs at hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some, renameGate] at hi
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
      apply wireBound
      apply hC.2.1 j hj i'
      change i' ∈ (C.gates.getD j ⟨.or, []⟩).inputs
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hi'
    · intro g hg
      change g ∈ C.gates.map (renameGate k) at hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      simpa [renameGate] using hC.2.2 g' hg'
  have dEval (k : Fin 26) (x : Fin 26 → Bool) :
      (D k).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (shift k i))) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have wireAgree (gates : List Gate) (xs ys : List Bool)
        (hlen : xs.length = ys.length) (hn : 26 ≤ xs.length)
        (hbits : ∀ i, xs.getD (wire k i) false = ys.getD i false) :
        ∀ i, (List.foldl step xs (gates.map (renameGate k))).getD (wire k i) false =
          (List.foldl step ys gates).getD i false := by
      induction gates generalizing xs ys with
      | nil => exact hbits
      | cons g gates ih =>
        have hv : (renameGate k g).op.eval ((renameGate k g).inputs.map fun i => xs.getD i false) =
            g.op.eval (g.inputs.map fun i => ys.getD i false) := by
          simp only [renameGate, List.map_map]
          congr 1
          exact List.map_congr_left (fun i _ => hbits i)
        simp only [List.map_cons, List.foldl_cons]
        apply ih
        · simp [step, hlen]
        · simp [step]; omega
        · intro i
          dsimp only [step]
          rw [hv]
          by_cases h : i < 26
          · have hw : wire k i < xs.length := by
              have hh : wire k i < 26 := by simp [wire, h]
              omega
            have hy : i < ys.length := by omega
            rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hy]
            exact hbits i
          · have hw : wire k i = i := by simp [wire, h]
            rw [hw]
            by_cases hi : i < ys.length
            · rw [List.getD_append _ _ _ _ (hlen.symm ▸ hi), List.getD_append _ _ _ _ hi]
              simpa only [hw] using hbits i
            · rw [List.getD_append_right _ _ _ _ (by omega),
                List.getD_append_right _ _ _ _ (by omega), hlen]
    unfold D Circuit.eval Circuit.wires
    exact wireAgree C.gates _ _ (by simp) (by simp) (by
      intro i
      by_cases h : i < 26
      · have hs := (shift k ⟨i, h⟩).isLt
        simp only [wire, dite_eq_left h, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
          dite_eq_left hs, Option.getD_some]
      · simp only [wire, dite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
          Option.getD_none]) C.output

  obtain ⟨bij,zero,pres⟩ := symmetry v
  refine ⟨shift v,D v,bij,zero,dModel v,dSize v,dEval v,?_⟩
  intro x
  rw [toGraph,toGraph]
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    exact ⟨_,_,(pres a b).mpr h,ha,hb⟩
  · rintro ⟨a,b,h,ha,hb⟩
    obtain ⟨a,rfl⟩ := bij.surjective a
    obtain ⟨b,rfl⟩ := bij.surjective b
    exact ⟨a,b,(pres a b).mp h,ha,hb⟩

end PEqualNP.Outside.L_meta_18828

theorem PEqualNP.Outside.L_meta_18828 : have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (26 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → ∃ (x5 : Fin (26 : ℕ) → Fin (26 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), Function.Bijective x5 ∧ x5 x2 = (0 : Fin (26 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ x6.size = x3.size ∧ (∀ (x7 : Fin (26 : ℕ) → Bool), x6.eval (List.ofFn x7) = x3.eval (List.ofFn (x7 ∘ x5))) ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), x1 (x7 ∘ x5) ↔ x1 x7 :=
  PEqualNP.Outside.L_meta_18828.transport
