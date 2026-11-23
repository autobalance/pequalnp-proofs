import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1035_refutation_aux

open PEqualNP.CircuitLowerBounds

abbrev W := BitVec 64

def inputs : List W :=
  [12297829382473034410, 14757395258967641292, 17361641481138401520,
    18374966859414961920, 18446462603027742720, 18446744069414584320]

def requestedPrefix : List W :=
  [14699973487531969536, 18432388630850633676, 12297829379609722880,
    17197820544402115584, 18441958926089912302, 18446744073708437486,
    12288259087233755784, 18446462594437808126, 18084480250975681272,
    18446181128050966528, 18084480250974632680, 18373277983783321320]

def target : W := 18445335577839206120

def base : Finset W := (0 :: BitVec.allOnes 64 :: inputs ++ requestedPrefix).toFinset

def read (w : List W) (i : ℕ) : W := w.getD i 0

def evaluate (w : List W) (g : Gate) : W :=
  match g.op with
  | .and => (g.inputs.map (read w)).foldr (· &&& ·) (BitVec.allOnes 64)
  | .or => (g.inputs.map (read w)).foldr (· ||| ·) 0
  | .not => ~~~read w (g.inputs.headD w.length)
  | _ => 0

def trace (w : List W) : List Gate → List W
  | [] => []
  | g :: gs => let v := evaluate w g; v :: trace (w ++ [v]) gs

def resulting (gs : List Gate) : List W := inputs ++ trace inputs gs

lemma trace_length (ws : List W) (gs : List Gate) : (trace ws gs).length = gs.length := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => simp only [trace, List.length_cons, ih]

def monoBasis (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def boolBasis (g : Gate) : Prop := g.op = .and ∨ g.op = .or ∨ g.op = .not

lemma val_getD (w : List W) (r i : ℕ) :
    (read w i).getLsbD r = (w.map (fun z => z.getLsbD r)).getD i false := by
  by_cases h : i < w.length
  · simp [read, h]
  · have hle : w.length ≤ i := by omega
    simp [read, hle]

lemma and_row (w : List W) (r : ℕ) (hr : r < 64) (is : List ℕ) :
    ((is.map (read w)).foldr (· &&& ·) (BitVec.allOnes 64)).getLsbD r =
      (is.map (fun i => (w.map fun z => z.getLsbD r).getD i false)).all id := by
  induction is with
  | nil =>
      simp only [List.map_nil, List.foldr_nil, List.all_nil, BitVec.getLsbD_allOnes,
        decide_eq_true hr]
  | cons i is ih =>
      simp only [List.map_cons, List.foldr_cons, BitVec.getLsbD_and, val_getD,
        List.all_cons, id_eq, ih]

lemma or_row (w : List W) (r : ℕ) (is : List ℕ) :
    ((is.map (read w)).foldr (· ||| ·) 0).getLsbD r =
      (is.map (fun i => (w.map fun z => z.getLsbD r).getD i false)).any id := by
  induction is with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.foldr_cons, BitVec.getLsbD_or, val_getD,
        List.any_cons, id_eq, ih]

lemma eval_row (w : List W) (r : ℕ) (hr : r < 64) (g : Gate) (hg : boolBasis g) :
    (evaluate w g).getLsbD r =
    g.op.eval (g.inputs.map fun i => (w.map fun z => z.getLsbD r).getD i false) := by
  rcases hg with h | h | h
  · simp only [evaluate, h, GateOp.eval, and_row _ _ hr]
  · simp only [evaluate, h, GateOp.eval, or_row]
  · simp only [evaluate, h, BitVec.getLsbD_not, decide_eq_true hr, Bool.true_and]
    cases his : g.inputs with
    | nil => simp [GateOp.eval, hr, read]
    | cons i is =>
        simp only [GateOp.eval, List.headD_cons, List.map_cons, val_getD]

def asRow (r : Fin 64) : Fin 6 → Bool := fun i => r.val.testBit i.val

lemma inputs_row (r : Fin 64) :
    inputs.map (fun z => z.getLsbD r.val) = List.ofFn (asRow r) := by
  revert r
  decide

lemma trace_row (w : List W) (gs : List Gate) (r : Fin 64)
    (hb : ∀ g ∈ gs, boolBasis g) :
    (w ++ trace w gs).map (fun z => z.getLsbD r.val) =
    gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
      (w.map fun z => z.getLsbD r.val) := by
  induction gs generalizing w with
  | nil => simp [trace]
  | cons g gs ih =>
      have hg := hb g (by simp)
      have hgs : ∀ k ∈ gs, boolBasis k := fun k hk => hb k (List.mem_cons_of_mem _ hk)
      rw [show w ++ trace w (g :: gs) =
          (w ++ [evaluate w g]) ++ trace (w ++ [evaluate w g]) gs by
          simp [trace, List.append_assoc], ih _ hgs]
      simp only [List.foldl_cons, List.map_append, List.map_cons, List.map_nil,
        eval_row w _ r.isLt g hg]

lemma output_row (gs : List Gate) (o : ℕ) (r : Fin 64) (hb : ∀ g ∈ gs, boolBasis g) :
    (read (resulting gs) o).getLsbD r.val =
      Circuit.eval ⟨gs, o⟩ (List.ofFn (asRow r)) := by
  rw [val_getD, resulting, trace_row _ _ _ hb, inputs_row]
  rfl

def Allowed (s : Finset W) (x : W) : Prop :=
  x ∈ s ∨ ∃ a ∈ s, ∃ b ∈ s, x = (a &&& b) ∨ x = (a ||| b)

lemma allow_mono {s t : Finset W} {x : W} (h : s ⊆ t) : Allowed s x → Allowed t x := by
  rintro (hx | ⟨a, ha, b, hb, hx⟩)
  · exact Or.inl (h hx)
  · exact Or.inr ⟨a, h ha, b, h hb, hx⟩

lemma read_mem {w : List W} {s : Finset W} (hz : (0 : W) ∈ s)
    (hw : ∀ v ∈ w, v ∈ s) (i : ℕ) : read w i ∈ s := by
  by_cases hi : i < w.length
  · rw [read, List.getD_eq_getElem _ _ hi]
    exact hw _ (List.getElem_mem hi)
  · have hl : w.length ≤ i := by omega
    simpa [read, List.getD_eq_default, hl] using hz

lemma orZero (x : W) : x ||| (0 : W) = x := BitVec.or_zero

lemma gate_allowed {w : List W} {s : Finset W} (hz : (0 : W) ∈ s)
    (ho : BitVec.allOnes 64 ∈ s) (hw : ∀ v ∈ w, v ∈ s)
    (g : Gate) (hg : monoBasis g) : Allowed s (evaluate w g) := by
  obtain ⟨hop, hl⟩ := hg
  have h (i : ℕ) := read_mem hz hw i
  rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · rcases hop with he | he <;> simp only [evaluate, he, hi, List.map_nil, List.foldr_nil]
    · exact Or.inl ho
    · exact Or.inl hz
  · have hh : Allowed s (read w a) := Or.inl (h a)
    rcases hop with he | he <;>
      simpa only [evaluate, he, hi, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, BitVec.and_allOnes, orZero] using hh
  · rcases hop with he | he
    · have hh : Allowed s (read w a &&& read w b) := Or.inr ⟨_, h a, _, h b, Or.inl rfl⟩
      simpa only [evaluate, he, hi, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, BitVec.and_allOnes, orZero] using hh
    · have hh : Allowed s (read w a ||| read w b) := Or.inr ⟨_, h a, _, h b, Or.inr rfl⟩
      simpa only [evaluate, he, hi, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, BitVec.and_allOnes, orZero] using hh
  · simp [hi] at hl

def Plan (s : Finset W) : List W → Prop
  | [] => True
  | v :: vs => Allowed s v ∧ Plan (insert v s) vs

def extra (gs : List Gate) : List W := (trace inputs gs).filter (fun v => !(decide (v ∈ base)))

lemma plan_filter (gs : List Gate) (w : List W) (s : Finset W)
    (hs : base ⊆ s) (hw : ∀ v ∈ w, v ∈ s)
    (hg : ∀ g ∈ gs, monoBasis g) :
    Plan s ((trace w gs).filter fun v => !(decide (v ∈ base))) := by
  induction gs generalizing w s with
  | nil => trivial
  | cons g gs ih =>
      have htail : ∀ k ∈ gs, monoBasis k := fun k hk => hg k (List.mem_cons_of_mem _ hk)
      let v := evaluate w g
      have hz : (0 : W) ∈ base := by decide
      have ho : BitVec.allOnes 64 ∈ base := by decide
      by_cases hv : v ∈ base
      · have hws : ∀ u ∈ w ++ [v], u ∈ s := by
          intro u hu
          rcases List.mem_append.mp hu with hu | hu
          · exact hw _ hu
          · simpa using (List.mem_singleton.mp hu) ▸ hs hv
        have h := ih (w ++ [v]) s hs hws htail
        simpa [trace, v, hv] using h
      · have hws : ∀ u ∈ w ++ [v], u ∈ insert v s := by
          intro u hu
          rcases List.mem_append.mp hu with hu | hu
          · exact Finset.mem_insert_of_mem (hw _ hu)
          · simp [List.mem_singleton.mp hu]
        have h := ih (w ++ [v]) (insert v s)
          (fun _ hu => Finset.mem_insert_of_mem (hs hu)) hws htail
        have ha := gate_allowed (hs hz) (hs ho) hw g (hg g (by simp))
        simpa [trace, v, hv, Plan] using And.intro ha h

def mix (s t : List W) : List W :=
  s.flatMap (fun a => t.flatMap (fun b => [a &&& b, a ||| b]))

def baseList : List W := 0 :: BitVec.allOnes 64 :: inputs ++ requestedPrefix

-- These six input rows suffice for the finite lower-bound computation.
def sample : List ℕ := [17, 50, 24, 20, 4, 6]

def project (x : W) : W :=
  (BitVec.ofBoolListLE (sample.map x.getLsbD)).setWidth' (by simp [sample])

lemma project_bits (x : W) (i : ℕ) :
    (project x).getLsbD i = (sample[i]?).elim false (fun r => x.getLsbD r) := by
  simp only [project, BitVec.getLsbD_setWidth', BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  cases sample[i]? <;> rfl

lemma project_and (x y : W) : project (x &&& y) = project x &&& project y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, project_bits]
  cases sample[i]? <;> simp

lemma project_or (x y : W) : project (x ||| y) = project x ||| project y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_or, project_bits]
  cases sample[i]? <;> simp

def smallBaseList : List W := [0, 1, 2, 4, 15, 32, 34, 38, 39, 56, 63]

def smallBase : Finset W := smallBaseList.toFinset

def smallTarget : W := 45

lemma project_target : project target = smallTarget := by decide

lemma project_base (x : W) (hx : x ∈ base) : project x ∈ smallBase := by
  have check : (baseList.map project).all (fun v => decide (v ∈ smallBase)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp check _ (List.mem_map_of_mem (f := project)
    (List.mem_toFinset.mp hx)))

lemma project_plan (s t : Finset W) (xs : List W)
    (hs : ∀ r ∈ s, project r ∈ t) (hp : Plan s xs) : Plan t (xs.map project) := by
  induction xs generalizing s t with
  | nil => trivial
  | cons v vs ih =>
      have hl : Allowed s v := hp.1
      have hstep : Allowed t (project v) := by
        rcases hl with hv | ⟨x, hx, y, hy, rfl | rfl⟩
        · exact Or.inl (hs v hv)
        · exact Or.inr ⟨_, hs x hx, _, hs y hy, Or.inl (project_and x y)⟩
        · exact Or.inr ⟨_, hs x hx, _, hs y hy, Or.inr (project_or x y)⟩
      refine ⟨hstep, ih _ _ ?_ hp.2⟩
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hs r hr)

def one : List W := (smallBaseList ++ mix smallBaseList smallBaseList).eraseDups

def two : List W := (one ++ mix one smallBaseList).eraseDups

lemma incl_base {a : W} (h : a ∈ smallBase) : a ∈ one := by
  apply List.mem_eraseDups.mpr
  exact List.mem_append_left _ (List.mem_toFinset.mp h)

lemma incl_one {a : W} (h : a ∈ one) : a ∈ two := by
  exact List.mem_eraseDups.mpr (List.mem_append_left _ h)

lemma mix_mem {s t : List W} {a b v : W} (ha : a ∈ s) (hb : b ∈ t)
    (hv : v = (a &&& b) ∨ v = (a ||| b)) : v ∈ mix s t := by
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, ?_⟩⟩
  rcases hv with rfl | rfl <;> simp

lemma allow_one {a : W} (h : Allowed smallBase a) : a ∈ one := by
  rcases h with hx | ⟨u, hu, v, hv, hh⟩
  · exact incl_base hx
  · exact List.mem_eraseDups.mpr (List.mem_append_right _ (mix_mem
      (List.mem_toFinset.mp hu) (List.mem_toFinset.mp hv) hh))

lemma allow_second {a b : W} (h : Allowed (insert a smallBase) b) :
    b ∈ one ∨ ∃ x ∈ smallBase, b = (a &&& x) ∨ b = (a ||| x) := by
  rcases h with hb | ⟨x, hx, y, hy, hh⟩
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact Or.inr ⟨0, by decide, Or.inr (by simp)⟩
    · exact Or.inl (incl_base hb)
  · rcases Finset.mem_insert.mp hx with hxe | hxm <;>
      rcases Finset.mem_insert.mp hy with hye | hym
    · subst x
      subst y
      exact Or.inr ⟨0, by decide, Or.inr (by simpa using hh)⟩
    · subst x
      exact Or.inr ⟨y, hym, hh⟩
    · subst y
      exact Or.inr ⟨x, hxm, by simpa only [BitVec.and_comm x a, BitVec.or_comm x a] using hh⟩
    · exact Or.inl (allow_one (Or.inr ⟨x, hxm, y, hym, hh⟩))

lemma second_mem {a b : W} (ha : a ∈ one)
    (hb : b ∈ one ∨ ∃ x ∈ smallBase, b = (a &&& x) ∨ b = (a ||| x)) : b ∈ two := by
  rcases hb with hb | ⟨x, hx, hh⟩
  · exact incl_one hb
  · exact List.mem_eraseDups.mpr (List.mem_append_right _ (mix_mem ha (List.mem_toFinset.mp hx) hh))

def PairSafe (a b : W) : Prop := (a &&& b) ≠ smallTarget ∧ (a ||| b) ≠ smallTarget

def noPair (s t : List W) : Bool :=
  s.all (fun a => t.all (fun b => decide ((a &&& b) ≠ smallTarget ∧ (a ||| b) ≠ smallTarget)))

set_option maxRecDepth 6000 in
set_option maxHeartbeats 6000000 in
lemma noPair_one : noPair one one = true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
lemma noPair_two : noPair two smallBaseList = true := by decide +kernel

lemma pair_of_check {s t : List W} (h : noPair s t = true)
    {a b : W} (ha : a ∈ s) (hb : b ∈ t) : PairSafe a b := by
  unfold noPair at h
  change (a &&& b) ≠ smallTarget ∧ (a ||| b) ≠ smallTarget
  exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp h) a ha)) b hb)

lemma target_not_two : smallTarget ∉ two := by
  intro ht
  have h0 : (0 : W) ∈ smallBaseList := by decide
  have hp := (pair_of_check noPair_two ht h0).2
  exact hp (by simp)

lemma pair_symm {a b : W} (h : PairSafe a b) : PairSafe b a := by
  simpa only [PairSafe, BitVec.and_comm b a, BitVec.or_comm b a] using h

lemma pair_same {a : W} (h : a ≠ smallTarget) : PairSafe a a := by
  simpa [PairSafe] using And.intro h h

lemma combine_and (a x : W) :
    a &&& (a &&& x) = a &&& x ∧ a ||| (a &&& x) = a := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD i <;> rfl

lemma combine_or (a x : W) :
    a &&& (a ||| x) = a ∧ a ||| (a ||| x) = a ||| x := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD i <;> rfl

lemma third_excluded {a b c : W}
    (ha : Allowed smallBase a) (hb : Allowed (insert a smallBase) b)
    (hc : Allowed (insert b (insert a smallBase)) c) : c ≠ smallTarget := by
  have ha₁ := allow_one ha
  have hbshape := allow_second hb
  have ha₂ := incl_one ha₁
  have hb₂ := second_mem ha₁ hbshape
  have xx (x : W) (hx : x ∈ two) : x ≠ smallTarget := fun h => target_not_two (h ▸ hx)
  have hab : PairSafe a b := by
    rcases hbshape with hb₁ | ⟨x, _, rfl | rfl⟩
    · exact pair_of_check noPair_one ha₁ hb₁
    · exact ⟨by rw [(combine_and a x).1]; exact xx _ hb₂,
        by rw [(combine_and a x).2]; exact xx _ ha₂⟩
    · exact ⟨by rw [(combine_or a x).1]; exact xx _ ha₂,
        by rw [(combine_or a x).2]; exact xx _ hb₂⟩
  have subsetTwo : ∀ x ∈ insert b (insert a smallBase), x ∈ two := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb₂
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha₂
      · exact incl_one (incl_base hx)
  rcases hc with hx | ⟨x, hx, y, hy, he⟩
  · exact xx _ (subsetTwo _ hx)
  have hx' := subsetTwo _ hx
  have hy' := subsetTwo _ hy
  have hs : PairSafe x y := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact pair_same (xx _ hb₂)
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact pair_symm hab
        · exact pair_of_check noPair_two hx' (List.mem_toFinset.mp hy)
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hab
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact pair_same (xx _ ha₂)
          · exact pair_of_check noPair_two hx' (List.mem_toFinset.mp hy)
      · exact pair_symm (pair_of_check noPair_two hy' (List.mem_toFinset.mp hx))
  rcases he with rfl | rfl
  · exact hs.1
  · exact hs.2

lemma short_plan (xs : List W) (hp : Plan smallBase xs) (hl : xs.length ≤ 3) :
    smallTarget ∉ xs := by
  have hz (x : W) (hx : x ∈ two) : x ≠ smallTarget := fun h => target_not_two (h ▸ hx)
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, ds⟩⟩⟩⟩
  · simp
  · have ha : Allowed smallBase a := hp.1
    simpa using Ne.symm (hz a (incl_one (allow_one ha)))
  · have ha : Allowed smallBase a := hp.1
    have hb : Allowed (insert a smallBase) b := hp.2.1
    have ea := hz a (incl_one (allow_one ha))
    have eb := hz b (second_mem (allow_one ha) (allow_second hb))
    simp [ea.symm, eb.symm]
  · have ha : Allowed smallBase a := hp.1
    have hb : Allowed (insert a smallBase) b := hp.2.1
    have hc : Allowed (insert b (insert a smallBase)) c := hp.2.2.1
    have ea := hz a (incl_one (allow_one ha))
    have eb := hz b (second_mem (allow_one ha) (allow_second hb))
    have ec := third_excluded ha hb hc
    simp [ea.symm, eb.symm, ec.symm]
  · simp only [List.length_cons] at hl
    omega

-- The first twelve gate values and the final gate value are the requested outputs.
def withNot : List Gate :=
  [⟨.and, [1, 3]⟩, ⟨.or, [3, 1]⟩, ⟨.and, [5, 0]⟩, ⟨.or, [6, 8]⟩,
   ⟨.or, [0, 7]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 10]⟩,
   ⟨.or, [2, 12]⟩, ⟨.and, [13, 4]⟩, ⟨.and, [14, 11]⟩, ⟨.or, [9, 16]⟩,
   ⟨.not, [1]⟩, ⟨.and, [15, 18]⟩, ⟨.or, [17, 19]⟩]

def positive : List Gate := withNot.take 12 ++
  [⟨.or, [2, 0]⟩, ⟨.or, [18, 3]⟩, ⟨.and, [19, 4]⟩, ⟨.or, [17, 20]⟩]

def outPos (j : Fin 13) : ℕ := if j.val < 12 then 6 + j.val else 21

def outNot (j : Fin 13) : ℕ := if j.val < 12 then 6 + j.val else 20

def outputMask (j : Fin 13) : W := (requestedPrefix ++ [target]).getD j.val 0

def family (j : Fin 13) (x : Fin 6 → Bool) : Bool :=
  Circuit.eval ⟨positive, outPos j⟩ (List.ofFn x)

lemma witness_posBasis : ∀ g ∈ positive, monoBasis g := by
  intro g hg
  simp only [positive, withNot, List.take_succ_cons, List.take_zero, List.nil_append,
    List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [monoBasis]

lemma witness_boolBasis : ∀ g ∈ withNot, boolBasis g ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [withNot, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [boolBasis]

lemma witness_one : ∀ i j : Fin withNot.length,
    (withNot.get i).op = .not → (withNot.get j).op = .not → i = j := by
  have only (i : Fin withNot.length) (h : (withNot.get i).op = .not) :
      i = ⟨12, by decide⟩ := by
    fin_cases i <;> simp [withNot] at h ⊢
  intro i j hi hj
  exact (only i hi).trans (only j hj).symm

lemma pos_mask (j : Fin 13) : read (resulting positive) (outPos j) = outputMask j := by
  revert j
  decide

lemma not_mask (j : Fin 13) : read (resulting withNot) (outNot j) = outputMask j := by
  revert j
  decide

lemma row_surj (x : Fin 6 → Bool) : ∃ r : Fin 64, asRow r = x := by
  let bv := BitVec.ofBoolListLE (List.ofFn x)
  let r : Fin 64 := ⟨bv.toNat, by simpa using bv.isLt⟩
  refine ⟨r, ?_⟩
  funext i
  change bv.getLsbD i.val = x i
  rw [BitVec.getLsbD_ofBoolListLE]
  have hi : i.val < (List.ofFn x).length := by simpa using i.isLt
  rw [List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

lemma mono_boolBasis {g : Gate} (h : monoBasis g) : boolBasis g := by
  rcases h.1 with he | he
  · exact Or.inl he
  · exact Or.inr (Or.inl he)

lemma same_family (j : Fin 13) (x : Fin 6 → Bool) :
    Circuit.eval ⟨withNot, outNot j⟩ (List.ofFn x) = family j x := by
  obtain ⟨r, rfl⟩ := row_surj x
  rw [family, ← output_row _ _ _ (fun g hg => (witness_boolBasis g hg).1),
    ← output_row _ _ _ (fun g hg => mono_boolBasis (witness_posBasis g hg)),
    not_mask, pos_mask]

def LeWires (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ i : ℕ, u.getD i false ≤ v.getD i false

lemma le_all (u v : List Bool) (h : LeWires u v) (is : List ℕ) :
    (is.map (fun i => u.getD i false)).all id ≤ (is.map (fun i => v.getD i false)).all id := by
  induction is with
  | nil => simp
  | cons i is ih =>
      have hi := h.2 i
      simp only [List.map_cons, List.all_cons, id_eq]
      cases hu : u.getD i false <;> cases hv : v.getD i false <;> simp_all
      exact ((by decide : ¬ true ≤ false) hi).elim

lemma le_any (u v : List Bool) (h : LeWires u v) (is : List ℕ) :
    (is.map (fun i => u.getD i false)).any id ≤ (is.map (fun i => v.getD i false)).any id := by
  induction is with
  | nil => simp
  | cons i is ih =>
      have hi := h.2 i
      simp only [List.map_cons, List.any_cons, id_eq]
      cases hu : u.getD i false <;> cases hv : v.getD i false <;> simp_all
      exact ((by decide : ¬ true ≤ false) hi).elim

lemma le_snoc {u v : List Bool} {a b : Bool} (h : LeWires u v) (hab : a ≤ b) :
    LeWires (u ++ [a]) (v ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  have hh : u.length = v.length := h.1
  by_cases hi : i < u.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hi, List.getElem?_append_left (hh ▸ hi)]
    exact h.2 i
  · have hle : u.length ≤ i := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right hle, List.getElem?_append_right (hh ▸ hle), hh]
    cases i - v.length <;> simp [hab]

lemma le_fold (gs : List Gate) (u v : List Bool) (h : LeWires u v)
    (hg : ∀ g ∈ gs, monoBasis g) :
    LeWires (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih _ _ (le_snoc h ?_) (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      rcases (hg g (by simp)).1 with he | he
      · simpa only [he, GateOp.eval] using le_all u v h g.inputs
      · simpa only [he, GateOp.eval] using le_any u v h g.inputs

lemma family_mono (j : Fin 13) (x y : Fin 6 → Bool) (h : ∀ i, x i ≤ y i) :
    family j x ≤ family j y := by
  have hw : LeWires (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hi : i < 6
    · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi,
        Option.getD_some] using h ⟨i, hi⟩
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hi,
        Option.getD_none, le_refl]
  exact (le_fold positive _ _ hw witness_posBasis).2 (outPos j)

lemma mask_data :
    (∀ j : Fin 13, outputMask j ≠ 0 ∧ outputMask j ∉ inputs) ∧
      (∀ j : Fin 12, outputMask j.castSucc ∈ base) ∧
      (∀ r : W, r ∈ requestedPrefix ↔ ∃ j : Fin 12, outputMask j.castSucc = r) := by
  constructor
  · decide
  constructor
  · decide
  · intro r
    constructor
    · intro h
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
      refine ⟨⟨i, ?_⟩, ?_⟩
      · exact hi
      · change (requestedPrefix ++ [target]).getD i 0 = r
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
          List.getElem?_eq_getElem hi]
        exact he
    · rintro ⟨j, hj⟩
      have hi : j.val < requestedPrefix.length := j.isLt
      rw [← hj]
      change (requestedPrefix ++ [target]).getD j.val 0 ∈ requestedPrefix
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, hi]

lemma read_eq_mem {ws : List W} {i : ℕ} {r : W} (he : read ws i = r) (hz : r ≠ 0) :
    r ∈ ws := by
  by_cases hi : i < ws.length
  · have hh : read ws i ∈ ws := by simp [read, hi]
    exact he ▸ hh
  · have hl : ws.length ≤ i := by omega
    exact (hz (by simpa [read, hl] using he.symm)).elim

lemma fixed_output (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, monoBasis g)
    (he : ∀ j x, Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = family j x) (j : Fin 13) :
    outputMask j ∈ trace inputs gs := by
  have hread : read (resulting gs) (out j) = outputMask j := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 64 := ⟨i, hi⟩
    change (read (resulting gs) (out j)).getLsbD r.val = (outputMask j).getLsbD r.val
    rw [output_row _ _ _ (fun g hg' => mono_boolBasis (hg g hg')), he, family,
      ← output_row _ _ _ (fun g hg' => mono_boolBasis (witness_posBasis g hg')), pos_mask]
  have hmem := read_eq_mem hread (mask_data.1 j).1
  exact (List.mem_append.mp hmem).resolve_left (mask_data.1 j).2

-- The twelve distinct initial outputs must use twelve distinct gate positions.
lemma extra_count (gs : List Gate) (out : Fin 13 → ℕ) (hsize : gs.length ≤ 15)
    (hg : ∀ g ∈ gs, monoBasis g)
    (he : ∀ j x, Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = family j x) :
    (extra gs).length ≤ 3 := by
  let kept := (trace inputs gs).filter (fun w => decide (w ∈ base))
  have hsub : requestedPrefix.toFinset ⊆ kept.toFinset := by
    intro r hr
    obtain ⟨j, rfl⟩ := (mask_data.2.2 r).mp (List.mem_toFinset.mp hr)
    exact List.mem_toFinset.mpr (List.mem_filter.mpr
      ⟨fixed_output gs out hg he j.castSucc, decide_eq_true (mask_data.2.1 j)⟩)
  have hlen : 12 ≤ kept.length := by
    calc
      12 = requestedPrefix.toFinset.card := by decide
      _ ≤ kept.toFinset.card := Finset.card_le_card hsub
      _ ≤ kept.length := List.toFinset_card_le kept
  have hsum : kept.length + (extra gs).length = gs.length := by
    have hh := (List.length_eq_countP_add_countP (l := trace inputs gs)
      (fun w => decide (w ∈ base))).symm
    simp only [kept, extra, List.countP_eq_length_filter, trace_length] at hh ⊢
    convert hh using 3
    congr 1
  omega

lemma no_small_positive (gs : List Gate) (out : Fin 13 → ℕ) (hsize : gs.length ≤ 15)
    (hg : ∀ g ∈ gs, monoBasis g)
    (he : ∀ j x, Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = family j x) : False := by
  have hm := fixed_output gs out hg he (12 : Fin 13)
  have ht : target ∉ base := by decide
  have hmem : target ∈ extra gs := List.mem_filter.mpr ⟨hm, by simp [ht]⟩
  have hplan : Plan base (extra gs) := plan_filter _ _ _ (by exact fun _ h => h)
    (by
      intro w hw
      exact List.mem_toFinset.mpr (by simp [hw]))
    hg
  have hbad : smallTarget ∈ (extra gs).map project := by
    rw [← project_target]
    exact List.mem_map_of_mem hmem
  exact short_plan ((extra gs).map project) (project_plan _ _ _ project_base hplan)
    (by simpa only [List.length_map] using extra_count gs out hsize hg he) hbad

end PEqualNP.Outside.L_meta_1035_refutation_aux

theorem PEqualNP.Outside.L_meta_1035_refutation : ¬ (∀ (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool), n ≤ 7 → (∀ (j : Fin m) (x y : Fin n → Bool), (∀ i : Fin n, x i ≤ y i) → f j x ≤ f j y) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out j⟩ (List.ofFn x) = f j x) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' j⟩ (List.ofFn x) = f j x) ∧ gates'.length ≤ gates.length) := by
  intro h
  open PEqualNP.Outside.L_meta_1035_refutation_aux in
  have result := h 6 13 family (by decide) family_mono withNot outNot
    ⟨witness_boolBasis, witness_one, same_family⟩
  obtain ⟨gs, out, hb, he, hsz⟩ := result
  exact PEqualNP.Outside.L_meta_1035_refutation_aux.no_small_positive gs out (by exact hsz) hb he
