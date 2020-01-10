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

Require Import order.


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


Section Def.

Variable (u : unit) (Ord : orderType u).

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
  if n is n'.+1 then
     [finType of {set (char_type n') * (char_type n')}]
  else [finType of bool].

Fixpoint char_rec n P : char_type n :=
  if n is n'.+1 then
    [set Cpair |
     `[exists x in P, (char_rec n' (down P x), char_rec n' (up P x)) == Cpair ]]
  else `[exists x, x \in P].
Definition char n P := nosimpl (char_rec n P).

Lemma char0P P : reflect (exists x, x \in P) (char 0 P).
Proof. exact/existsbP. Qed.

Lemma mem_charP n P l r :
  reflect
    (exists x, [/\ x \in P, char n (down P x) = l & char n (up P x) = r])
    ((l, r) \in char n.+1 P).
Proof.
apply (iffP idP); rewrite /char /= inE.
- by move/existsbP => [x /andP [xinP /eqP [<- <-]]]; exists x.
- move=> [x [xinP <- <-]]; apply/existsbP; exists x.
  exact/andP.
Qed.

Lemma char0_pred0 : char 0 pred0 = false.
Proof. by apply/char0P => [] [x]; rewrite inE. Qed.
Lemma char0_true P : char 0 P -> P <> pred0.
Proof.
move/char0P => [x xinP eqP0].
by move: xinP; rewrite eqP0 inE.
Qed.

Lemma char1_pred0 P : char 1 pred0 = set0.
Proof.
apply/setP => [[l r]].
rewrite [RHS]inE; apply/negP => /(mem_charP (n := 0)) [x []].
by rewrite inE.
Qed.

(* James's 6-th lemma *)
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
  apply/negP => /(mem_charP (n := 0)) /= [x []].
  rewrite inE => /eqP ->{x}.
  by rewrite down_pred1 char0_pred0.
case: b; rewrite eqE /= /eqb /=.
- apply/negP => /(mem_charP (n := 0)) /= [x []].
  rewrite inE => /eqP ->{x} _.
  by rewrite up_pred1 char0_pred0.
- apply/(mem_charP (n := 0)); exists x0.
  by rewrite inE down_pred1 up_pred1 char0_pred0.
Qed.

(* James's 7-th lemma *)
Lemma charFF P :
  (false, false) \in char 1 P -> exists x, P = pred1 x.
Proof.
move/mem_charP => [x [xinP /char0P downP /char0P upP]].
exists x; apply funext => y.
rewrite [RHS]inE /= eq_sym.
have /= -> := (topredE y P).
case: (ltgtP x y) => [ltxy|ltyx|<- //].
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

(* James's 5-th lemma *)
Lemma charFT P :
  (false, true) \in char 1 P ->
  (true, true) \in char 1 P \/ (true, false) \in char 1 P.
Proof.
move/mem_charP => [x0 [x0inP /char0P downP /char0P [x1 /upP[x1inP lt01]]]].
case: (boolP ((true, true) \in char 1 P)) => Htt; [left | right] => //.
apply/mem_charP; exists x1; split; first by [].
- apply/char0P; exists x0.
  by rewrite -up_down //; apply/upP.
- apply/char0P => [] [x2 /upP [x2inP lt12]].
  move: Htt => /negP; apply; apply/mem_charP.
  exists x1; split => //; apply/char0P.
  + by exists x0; apply/upP.
  + by exists x2; apply/upP.
Qed.

End Def.


Section Dual.

Variable (u : unit) (Ord : orderType u).
Implicit Type (x t : Ord) (P : pred Ord).

Local Arguments char {u} Ord.
Local Arguments down {u} Ord.
Local Arguments up {u} Ord.

Let OrdC := [orderType of Ord^d].


Lemma down_dual P x : down OrdC P x = up Ord P x.
Proof. by apply predext => y; rewrite !inE. Qed.
Lemma up_dual P x : up OrdC P x = down Ord P x.
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


Lemma char0_dual P : char Ord 0 P = char OrdC 0 P.
Proof. by apply/char0P/char0P => [] [x xinP]; exists x. Qed.

Lemma char_dual n P : char Ord n P = rev_char (char OrdC n P).
Proof.
elim: n P => [|n IHn] P /=; first exact: char0_dual.
apply/setP => /= [[chdown chup]].
apply/mem_charP/imsetP => /= [[x [xinP dE uE]] | [[chd chu]]].
- exists (rev_char chup, rev_char chdown).
  + apply/mem_charP => /=.
    by exists x; split; rewrite // -?uE -?dE IHn !rev_charK ?downdual ?updual.
  + by rewrite /= !rev_charK.
- move=> /mem_charP [x [xinP <-{chd} <-{chu}]] [->{chdown} ->{chup}].
  by exists x; rewrite -!IHn ?downdual ?updual.
Qed.

End Dual.

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
by rewrite -[LHS]rev_charK -char_dual char1_nat /= imsetU1 imset_set1.
Qed.


Lemma char0_nat2 : char 0 [pred i | i < 2] = true.
Proof. by apply/char0P; exists 0. Qed.

Lemma char1_nat2 :
  char 1 [pred i | i < 2] = [set (false, true); (true, false)].
Proof.
apply/setP => [] [[|] [|]]; rewrite in_set2 ?eqE /= ?eqE /= ?/eqb /=.
- apply/negP => /(mem_charP (n := 0)) /= [] [|[|i]];
                  rewrite //= inE => [] [] // _.
  + by move=> /char0P/= [x]; rewrite !inE => /andP [].
  + move=> _ /char0P/= [x]; rewrite !inE => /andP [].
    by rewrite !ltEnat ltnS => /leq_ltn_trans {}H/H; rewrite ltnn.
- apply/(mem_charP (n := 0)) => /=.
  exists 1%N; split => //; apply/char0P => /=.
  + by exists 0.
  + move=> [x]; rewrite !inE => /andP [].
    by rewrite !ltEnat ltnS => /leq_ltn_trans {}H/H; rewrite ltnn.
- apply/(mem_charP (n := 0)) => /=.
  exists 0%N; split => //; apply/char0P => /=.
  + by move=> [x]; rewrite !inE => /andP [].
  + by exists 1%N.
- apply/negP => /(mem_charP (n := 0)) /= [] [|[|i]];
                  rewrite //= inE => [] [] // _.
  + by move=> _ /char0P/= H; apply: H; exists 1%N.
  + by move=> /char0P/= H _; apply: H; exists 0%N.
Qed.


Lemma char0_nat3 : char 0 [pred i | i < 3%N] = true.
Proof. by apply/char0P; exists 0. Qed.

Lemma char1_nat3 :
  char 1 [pred i | i < 3%N] = [set (false, true); (true, true); (true, false)].
Proof.
apply/setP => [] [[|] [|]]; rewrite ![in RHS]inE ?eqE /= ?eqE /= ?/eqb /=.
- apply/(mem_charP (n := 0)) => /=.
  exists 1%N; split => //; apply/char0P => /=.
  + by exists 0.
  + by exists 2.
- apply/(mem_charP (n := 0)) => /=.
  exists 2%N; split => //; apply/char0P => /=.
  + by exists 0.
  + move=> [x]; rewrite !inE => /andP [].
    by rewrite !ltEnat ltnS => /leq_ltn_trans {}H/H; rewrite ltnn.
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
