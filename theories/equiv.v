(******************************************************************************)
(*       Copyright (C) 2020 Florent Hivert <florent.hivert@lri.fr>            *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.
Open Scope order_scope.



Lemma predext (T : Type) (p1 p2 : simpl_pred T) : p1 = p2 <-> p1 =i p2.
Proof.
split => [-> x // | eqf].
case: p1 p2 eqf => [p1] [p2] eqf; suff -> : p1 = p2 by [].
by apply funext => x; have:= eqf x; rewrite !unfold_in /=.
Qed.


Section CanonicalEnumeration.

Lemma enum_bool : enum (bool : finType) = [:: true; false].
Proof. by rewrite enumT unlock. Qed.

Lemma enum_prod_bool_T (T : finType) :
  enum ((bool * T)%type : finType) =
  [seq (true, t) | t <- enum T] ++ [seq (false, t) | t <- enum T].
Proof. by rewrite enumT unlock /= /prod_enum enum_bool /= cats0. Qed.

Lemma enum_bool_bool :
  enum ((bool * bool)%type : finType) =
  [:: (true, true); (true, false); (false, true); (false, false) ].
Proof. by rewrite enum_prod_bool_T enum_bool. Qed.

Lemma eq_finset_enum (T : finType) (s1 s2 : {set T}) :
  (s1 == s2) = all (fun pr => (pr \in s1) == (pr \in s2)) (enum T).
Proof.
apply/eqP/allP => [-> // | Heq]; apply/setP => t; apply/eqP/Heq.
by rewrite mem_enum.
Qed.

End CanonicalEnumeration.


Section Def.

Context {u : unit} (Ord : orderType u).

Implicit Type (P : pred Ord).

Definition down P x := [predI P & [pred y | y < x]].
Definition up P x := [predI P & [pred y | y > x]].

Lemma downP P x y :
  reflect (y \in P /\ y < x) (y \in down P x).
Proof. by rewrite !inE; apply andP. Qed.

Lemma upP P x y :
  reflect (y \in P /\ x < y) (y \in up P x).
Proof. by rewrite !inE; apply andP. Qed.

Lemma up_pred0 x : up pred0 x = pred0.
Proof. by apply predext => y; rewrite !inE. Qed.
Lemma down_pred0 x : down pred0 x = pred0.
Proof. by apply predext => y; rewrite !inE. Qed.

Lemma up_pred1 x : up (pred1 x) x = pred0.
Proof.
apply predext => y; rewrite !inE. case: eqP => // -> /=.
by rewrite ltxx.
Qed.
Lemma down_pred1 x : down (pred1 x) x = pred0.
Proof.
apply predext => y; rewrite !inE; case: eqP => // -> /=.
by rewrite ltxx.
Qed.


Fixpoint char_type n : finType :=
  if n is n'.+1 then {set (char_type n') * (char_type n')} else bool.

Fixpoint char_rec n P : char_type n :=
  if n is n'.+1 then
    [set Cpair |
      `[< exists x,
            (x \in P) &&
              ((char_rec n' (down P x), char_rec n' (up P x)) == Cpair) >]]
  else `[< exists x, x \in P >].
Definition char n P := nosimpl (char_rec n P).

Lemma char0P P : reflect (exists x, x \in P) (char 0 P).
Proof. exact: (iffP (asboolP _)). Qed.

Lemma mem_charP n P l r :
  reflect
    (exists x, [/\ x \in P, char n (down P x) = l & char n (up P x) = r])
    ((l, r) \in char n.+1 P).
Proof.
apply (iffP idP); rewrite /char /= inE.
- by move/asboolP => [x /andP[xinP /eqP[<- <-]]]; exists x.
- move=> [x [xinP <- <-]]; apply/asboolP; exists x.
  exact/andP.
Qed.
Arguments mem_charP (n P l r) : clear implicits.

Lemma char0_pred0 : char 0 pred0 = false.
Proof. by apply/char0P => [] [x]; rewrite inE. Qed.
Lemma char0_true P : char 0 P -> P <> pred0.
Proof. by move/char0P => [x /[swap] ->]; rewrite inE. Qed.

Lemma char_pred0 n : char n.+1 pred0 = set0.
Proof.
apply/setP => [[l r]]; rewrite [RHS]inE.
apply/negP => /mem_charP [x []].
by rewrite inE.
Qed.

(** James's 6-th lemma *)
Lemma char1_eq0P P : char 1 P = set0 -> P = pred0.
Proof.
move=> ch1; apply funext => x /=.
apply/negP => Px.
suff : (char 0 (down P x), char 0 (up P x)) \in char 1 P.
  by rewrite ch1 inE.
by apply/mem_charP; exists x.
Qed.

Lemma char1_pred1 x0 : char 1 (pred1 x0) = [set (false, false)].
Proof.
apply/setP => [] [[|] /= b]; rewrite in_set1 ?eqE /=.
  apply/negP => /(mem_charP 0) /= [x []].
  rewrite inE => /eqP ->{x}.
  by rewrite down_pred1 char0_pred0.
case: b; rewrite eqE /= /eqb /=.
- apply/negP => /(mem_charP 0) /= [x []].
  rewrite inE => /eqP ->{x} _.
  by rewrite up_pred1 char0_pred0.
- apply/(mem_charP 0); exists x0.
  by rewrite inE down_pred1 up_pred1 char0_pred0.
Qed.

(** James's 7-th lemma *)
Lemma charFF P :
  (false, false) \in char 1 P -> exists x, P = pred1 x.
Proof.
move/(mem_charP 0) => [x [xinP /char0P downP /char0P upP]].
exists x; apply funext => y.
rewrite [RHS]inE /= eq_sym.
have /= -> := (topredE y P).
case: (ltgtP x y) => [ltxy | ltyx | <- //].
- apply/negP => yinP; apply upP; exists y.
  by rewrite !inE yinP ltxy.
- apply/negP => yinP; apply downP; exists y.
  by rewrite !inE yinP ltyx.
Qed.

Lemma charFFE P :
  (false, false) \in char 1 P -> char 1 P = [set (false, false)].
Proof. by move/charFF => [x ->]; apply char1_pred1. Qed.

Lemma up_down P x y :
  x \in P -> y \in P -> (y \in up P x) = (x \in down P y).
Proof. by rewrite !inE => -> ->. Qed.

(** James's 5-th lemma *)
Lemma charFT P :
  (false, true) \in char 1 P ->
  (true, true) \in char 1 P \/ (true, false) \in char 1 P.
Proof.
move/(mem_charP 0) => [x0 [x0inP /char0P downP /char0P [x1 /upP[x1inP lt01]]]].
case: (boolP ((true, true) \in char 1 P)) => Htt; [left | right] => //.
apply/(mem_charP 0); exists x1; split; first by [].
- apply/char0P; exists x0.
  by rewrite -up_down //; apply/upP.
- apply/char0P => [] [x2 /upP [x2inP lt12]].
  move: Htt => /negP; apply; apply/(mem_charP 0).
  exists x1; split => //; apply/char0P.
  + by exists x0; apply/upP.
  + by exists x2; apply/upP.
Qed.

End Def.


Section Dual.

Variable (u : unit) (Ord : orderType u).
Implicit Type (x t : Ord) (P : pred Ord).

Lemma down_dual P x : down (Ord := Ord^d) P x = up P x.
Proof. by apply predext => y; rewrite !inE. Qed.
Lemma up_dual P x : up (Ord := Ord^d) P x = down P x.
Proof. by apply predext => y; rewrite !inE. Qed.


Fixpoint rev_char n : char_type n -> char_type n :=
  if n is n'.+1 then
    fun ch => [set (rev_char C.2, rev_char C.1) | C in ch]
  else id.

Lemma rev_charK n : involutive (@rev_char n).
Proof.
elim: n => [|n IHn] P //=.
rewrite -imset_comp; apply/setP => [[chdown chup]] /=.
set f := (F in imset F _).
suff {chdown chup P} : f =1 id by move/eq_imset => ->; rewrite imset_id.
rewrite {}/f => [[chdown chup]] /=.
by rewrite !IHn.
Qed.

Lemma mem_rev_char n ch1 ch2 (ch : char_type n.+1) :
  ((ch1, ch2) \in rev_char ch) = ((rev_char ch2, rev_char ch1) \in ch).
Proof.
rewrite /=; apply/imsetP/idP => [[[c1 c2] /= cin [-> ->]] | rchin].
  by rewrite !rev_charK.
by exists (rev_char ch2, rev_char ch1); rewrite ?rev_charK.
Qed.

Lemma mem_rev_char1 (ch1 ch2 : bool) (ch : char_type 1) :
  ((ch1, ch2) \in rev_char ch) = ((ch2, ch1) \in ch).
Proof. by rewrite (@mem_rev_char 0). Qed.

Lemma char0_dual P : char (Ord := Ord) 0 P = char (Ord := Ord^d) 0 P.
Proof. by apply/char0P/char0P => [] [x xinP]; exists x. Qed.

Lemma char_dual n P :
  rev_char (char (Ord := Ord^d) n P) = char (Ord := Ord) n P.
Proof.
elim: n P => [|n IHn] P /=; first exact: char0_dual.
apply/setP => /= [[chdown chup]].
apply/imsetP/mem_charP => /= [ [[chd chu]] | [x [xinP dE uE]]].
- move=> /mem_charP [x [xinP <-{chd} <-{chu}]] [->{chdown} ->{chup}].
  by exists x; rewrite -!IHn ?downdual ?updual.
- exists (rev_char chup, rev_char chdown).
  + apply/mem_charP => /=.
    by exists x; split; rewrite // -?uE -?dE -IHn !rev_charK ?downdual ?updual.
  + by rewrite /= !rev_charK.
Qed.

End Dual.


Section CharPredicate.

Variables (u : unit) (Ord : orderType u).
Implicit Types (P : pred Ord) (ch : char_type 1).

Lemma charTF P :  (* Dual lemma of charFT *)
  (true, false) \in char 1 P ->
  (true, true) \in char 1 P \/ (false, true) \in char 1 P.
Proof. by rewrite -(char_dual 1 P) !mem_rev_char1; apply: charFT. Qed.

(** This is a characterization of sets which are of char 1 of some predicate *)
(*  However, we will show it only at the end !                               *)
Definition is_char1 :=
  [pred ch : char_type 1 | [&&
   ((false, false) \in ch) ==> (ch == [set (false, false)]),
   ((true, false) \in ch) ==> ((true, true) \in ch) || ((false, true) \in ch) &
   ((false, true) \in ch) ==> ((true, true) \in ch) || ((true, false) \in ch)
  ]].

Lemma is_char1_char1 P : is_char1 (char 1 P).
Proof.
apply/and3P; split; apply/implyP.
- by move/charFFE ->.
- by move/charTF => [] -> //; rewrite orbT.
- by move/charFT => [] -> //; rewrite orbT.
Qed.

End CharPredicate.



(********************************************)
(** Various examples for the classification *)

Lemma char0_nat : char 0 (@predT nat) = true.
Proof. by apply/char0P; exists 0. Qed.
Lemma char0_nat_dual : char 0 (@predT nat^d) = true.
Proof. by apply/char0P; exists 0. Qed.

Lemma char1_nat : char 1 (@predT nat) = [set (false, true); (true, true)].
Proof.
apply/setP => [] [[|] [|]]; rewrite in_set2 ?eqE /= ?eqE /= ?/eqb /=.
- apply/(mem_charP (n := 0)) => /=.
  exists 1%N; split => //; apply/char0P => /=.
  + by exists 0.
  + by exists 2.
- apply/negP => /(mem_charP (n := 0)) /= [x [_ _ /char0P]] /=; apply.
  by exists x.+1; rewrite !inE ltEnat /=.
- apply/(mem_charP (n := 0)) => /=.
  exists 0%N; split => //; apply/char0P => /=.
  + by move=> [].
  + by exists 1%N.
- apply/negP => /(mem_charP (n := 0)) /= [x [_ _ /char0P]] /=; apply.
  by exists x.+1; rewrite !inE ltEnat /=.
Qed.

Lemma char1_nat_dual :
  char 1 (@predT nat^d) = [set (true, false); (true, true)].
Proof.
by rewrite -[LHS]rev_charK char_dual char1_nat /= imsetU1 imset_set1.
Qed.

Lemma char0_down2 : char 0 (down predT 2) = true.
Proof. by apply/char0P; exists 0. Qed.

Lemma char1_down2 :
  char 1 (down predT 2) = [set (false, true); (true, false)].
Proof.
apply/setP => [] [[|] [|]]; rewrite in_set2 ?eqE /= ?eqE /= ?/eqb /=.
- apply/negP => /(mem_charP (n := 0)) /= [] [|[|i]];
                  rewrite //= inE => [] [] // _.
  + by move=> /char0P/= [x]; rewrite !inE => /andP [].
  + move=> _ /char0P/= [x]; rewrite !inE => /andP [].
    by rewrite !ltEnat /= ltnS => /leq_ltn_trans {}H/H; rewrite ltnn.
- apply/(mem_charP (n := 0)) => /=.
  exists 1%N; split => //; apply/char0P => /=.
  + by exists 0.
  + move=> [x]; rewrite !inE => /andP [].
    by rewrite !ltEnat /= ltnS => /leq_ltn_trans {}H/H; rewrite ltnn.
- apply/(mem_charP (n := 0)) => /=.
  exists 0%N; split => //; apply/char0P => /=.
  + by move=> [x]; rewrite !inE => /andP [].
  + by exists 1%N.
- apply/negP => /(mem_charP (n := 0)) /= [] [|[|i]];
                  rewrite //= inE => [] [] // _.
  + by move=> _ /char0P/= H; apply: H; exists 1%N.
  + by move=> /char0P/= H _; apply: H; exists 0%N.
Qed.


Lemma char0_down3plus n : char 0 (down predT n.+3) = true.
Proof. by apply/char0P; exists 0. Qed.
Lemma char0_down3 : char 0 (down predT 3) = true.
Proof. exact: char0_down3plus. Qed.

Lemma char1_down3plus n :
  char 1 (down predT n.+3) = [set (false, true); (true, true); (true, false)].
Proof.
apply/setP => [] [[|] [|]]; rewrite ![in RHS]inE ?eqE /= ?eqE /= ?/eqb /=.
- apply/(mem_charP (n := 0)) => /=.
  exists 1%N; split => //; apply/char0P => /=.
  + by exists 0.
  + by exists 2.
- apply/(mem_charP (n := 0)) => /=.
  exists n.+2; split.
  + by rewrite !inE //= ltEnat /= !ltnS.
  + by apply/char0P => /=; exists 0.
  + apply/char0P => /=[][x]; rewrite !inE => /andP [].
    by rewrite !ltEnat /= ltnS => /leq_ltn_trans /[apply]; rewrite ltnn.
- apply/(mem_charP (n := 0)) => /=.
  exists 0%N; split => //; apply/char0P => /=.
  + by move=> [x]; rewrite !inE => /andP [].
  + by exists 1%N.
- apply/negP => /(mem_charP (n := 0)) /= [] [|[|i]];
                  rewrite //= inE => [] [] // _.
  + by move=> _ /char0P/= H; apply: H; exists 1%N.
  + by move=> /char0P/= H _; apply: H; exists 0%N.
  + by move=> /char0P/= H _; apply: H; exists 0%N.
Qed.
Lemma char1_down3 :
  char 1 (down predT 3) = [set (false, true); (true, true); (true, false)].
Proof. exact: char1_down3plus. Qed.


From mathcomp Require Import ssralg ssrnum ssrint.

Lemma char0_int : char 0 (@predT int) = true.
Proof. by apply/char0P; exists 0%R. Qed.

Lemma char1_int : char 1 (@predT int) = [set (true, true)].
Proof.
apply/setP => [] [[|] [|]]; rewrite ![in RHS]inE ?eqE /= ?eqE /= ?/eqb /=.
- apply/(mem_charP (n := 0)) => /=.
  exists 0%R; split => //; apply/char0P => /=.
  + by exists (- 1)%R.
  + by exists 1%R.
- apply/negP => /(mem_charP (n := 0)) /= [i [_]].
  move=> _ /char0P/= H; apply: H; exists (i + 1)%R.
  apply/upP; split => //=.
  by rewrite ltzD1.
- apply/negP => /(mem_charP (n := 0)) /= [i [_]].
  move=> /char0P/= H _; apply: H; exists (i - 1)%R.
  apply/downP; split => //=.
  by rewrite Num.Theory.ltrBlDr ltzD1.
- apply/negP => /(mem_charP (n := 0)) /= [i [_]].
  move=> /char0P/= H _; apply: H; exists (i - 1)%R.
  apply/downP; split => //=.
  by rewrite Num.Theory.ltrBlDr ltzD1.
Qed.


(** The [char 1] classification *)
Section Classification1.

Variables (u : unit) (Ord : orderType u).
Implicit Type (x t : Ord) (P : pred Ord) (ch : char_type 1).

(** Predicate describing a subset of an ordered set *)
Record ordPred := OrdPred {
                      disp_ordPred : unit;
                      type_ordPred : orderType disp_ordPred;
                      pred_ordPred :> pred type_ordPred
                    }.

Definition classif1_order : seq ordPred := [::
     OrdPred (@pred0 nat);          (* empty     *)
     OrdPred (pred1 0%N);           (* {0}       *)
     OrdPred (down predT 2);        (* {0, 1}    *)
     OrdPred (down predT 3);        (* {0, 1, 2} *)
     OrdPred (@predT nat);          (* N         *)
     OrdPred (@predT nat^d);        (* -N        *)
     OrdPred (@predT int)           (* Z         *)
  ].
Definition classif1 :=
  [tuple of map (fun pr : ordPred => char 1 pr) classif1_order].
Definition classif1E := (char_pred0 nat, char1_pred1 0%N,
                char1_down2, char1_down3, char1_nat, char1_nat_dual, char1_int).

(** There are no duplicate in the classification *)
Proposition classif1_uniq : uniq classif1.
Proof.
rewrite /classif1 /classif1_order /= !classif1E /=.
by rewrite !inE !eq_finset_enum !enum_bool_bool /= !inE.
Qed.

Theorem is_char1E ch : (is_char1 ch) = (ch \in classif1).
Proof.
apply/idP/idP.
- (** Expand the definitions and the classification *)
  rewrite /classif1 /classif1_order /= !classif1E /=.
  (** Expand computationally equality of char 1 *)
  rewrite !inE !eq_finset_enum !enum_bool_bool /= !inE.
  (** case analysis *)
  by repeat case: (boolP (_ \in _)) => _; rewrite ?inE.
- rewrite !inE.
  by repeat move/orP => []; try (move/eqP->; exact: is_char1_char1).
Qed.

(** All characters are in the classification *)
Corollary classifP P : exists! i : 'I_7, char 1 P = tnth classif1 i.
Proof.
have /tnthP [i Hi] : char 1 P \in classif1.
  by rewrite -is_char1E; exact: is_char1_char1.
exists i; split => // j; rewrite {}Hi.
exact/tuple_uniqP/classif1_uniq.
Qed.

(** is_char1 decide if a (ch : char_type) is the characteristic of an actual P *)
Corollary is_char1P ch :
  reflect (exists P : ordPred, char 1 P = ch) (is_char1 ch).
Proof.
pose Z := (OrdPred (@pred0 bool)). (** to please nth *)
apply (iffP idP); last by move=> [P <-]; exact: is_char1_char1.
rewrite is_char1E => /tnthP [i ->].
exists (nth Z classif1_order i).
by rewrite /classif1 [RHS](tnth_nth (char 1 Z)) (nth_map Z).
Qed.

End Classification1.
