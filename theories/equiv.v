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

Variable (u : unit) (X : orderType u).

Implicit Type (P : pred X).

Definition down P x := [predI P & [pred y | y < x]].
Definition up P x := [predI P & [pred y | y > x]].

Lemma up_pred0 x : up pred0 x = pred0.
Proof. by apply predext => y; rewrite !inE. Qed.
Lemma down_pred0 x : down pred0 x = pred0.
Proof. by apply predext => y; rewrite !inE. Qed.

Lemma up_pred1 x : up (pred1 x) x = pred0.
Proof.
apply predext => y; rewrite !inE; case: eqP => // -> /=.
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

Lemma char0P P : reflect (exists x : X, x \in P) (char 0 P).
Proof. exact/existsbP. Qed.

Lemma mem_charP n P l r :
  reflect
    (exists x : X, [/\ x \in P, char n (down P x) = l & char n (up P x) = r])
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

Lemma char1_pred0 P : char 1 pred0 = finset.set0.
Proof.
apply/setP => [[l r]].
rewrite [RHS]inE; apply/negP => /(mem_charP (n := 0)) [x []].
by rewrite inE.
Qed.

Lemma char10P P : char 1 P = finset.set0 -> P = pred0.
Proof.
move=> ch1; apply funext => x /=.
apply/negP => Px.
suff : (char 0 (down P x), char 0 (up P x)) \in char 1 P.
  by rewrite ch1 inE.
by apply/mem_charP; exists x.
Qed.


Lemma char1pred1 x0 : char 1 (pred1 x0) = [set (false, false)].
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
Proof. by move/charFF => [x ->]; apply char1pred1. Qed.

End Def.

Lemma char0nat : char 0 (@predT nat) = true.
Proof. by apply/char0P; exists 0. Qed.

Lemma char1nat : char 1 (@predT nat) = [set (false, true); (true, true)].
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

