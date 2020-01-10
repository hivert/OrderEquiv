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
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import fintype finset.
From mathcomp Require Import boolp classical_sets.

Require Import order.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.

Open Scope order_scope.
Open Scope classical_set_scope.

Lemma clsetP X (E F : set X) : (E =1 F) <-> (E = F).
Proof.
split => EF.
- by apply eqEsubset => x; rewrite EF.
- by rewrite EF => x.
Qed.


Section Def.

Variable (u : unit) (X : orderType u).

Implicit Type E : set X.

Definition down E x := E `&` [set y | y < x].
Definition up   E x := E `&` [set y | x < y].


Lemma up0 x : up set0 x = set0.
Proof.
rewrite -subset0 => y /=.
by rewrite /up /setI /= /set0 => [[]].
Qed.

Lemma down0 x : down set0 x = set0.
Proof.
rewrite -subset0 => y /=.
by rewrite /down /setI /= /set0 => [[]].
Qed.

Lemma up1 x : up [set x] x = set0.
Proof.
rewrite -subset0 => y /=.
rewrite /setI /= /set0 /set1 => [[->]].
by rewrite ltxx.
Qed.
Lemma down1 x : down [set x] x = set0.
Proof.
rewrite -subset0 => y /=.
rewrite /setI /= /set0 /set1 => [[->]].
by rewrite ltxx.
Qed.

Fixpoint char_type n : finType :=
  if n is n'.+1 then
     [finType of {set (char_type n') * (char_type n')}]
  else [finType of bool].

Fixpoint char_rec n S : char_type n :=
  if n is n'.+1 then
    [set pc |
     `[exists x in S, (char_rec n' (down S x), char_rec n' (up S x)) == pc ]
    ]%SET
  else `[exists x, x \in S] : char_type 0.
Definition char n S := nosimpl (char_rec n S).

Lemma char0P E : reflect (exists x, x \in E) (char 0 E).
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

Lemma char0_pred0 : char 0 set0 = false.
Proof. by apply/char0P => [] [x]; rewrite in_setE /set0. Qed.
Lemma char0_true P : char 0 P -> P <> set0.
Proof.
move/char0P => [x xinP eqP0].
by move: xinP; rewrite eqP0 in_setE /set0.
Qed.

Lemma char1_pred0 : char 1 set0 = finset.set0.
Proof.
apply/setP => [[l r]].
rewrite [RHS]inE; apply/negP => /(mem_charP (n := 0)) [x []].
by rewrite in_setE.
Qed.

Lemma char10P E : char 1 E = finset.set0 -> E = set0.
Proof.
move=> ch1; rewrite -subset0 => x /=.
rewrite /set0 => Ex.
suff : (char 0 (down E x), char 0 (up E x)) \in char 1 E.
  by rewrite ch1 inE.
by apply/mem_charP; exists x; rewrite in_setE.
Qed.

Lemma char1pred1 x0 : char 1 [set x0] = [set (false, false)]%SET.
Proof.
apply/setP => [] [[|] /= b]; rewrite in_set1 ?eqE /=.
  apply/negP => /(mem_charP (n := 0)) /= [x []].
  rewrite in_setE => ->{x}.
  by rewrite down1 char0_pred0.
case: b; rewrite eqE /= /eqb /=.
- apply/negP => /(mem_charP (n := 0)) /= [x []].
  rewrite in_setE => ->{x} _.
  by rewrite up1 char0_pred0.
- apply/(mem_charP (n := 0)); exists x0.
  by rewrite in_setE /set1 down1 up1 char0_pred0.
Qed.

Lemma charFF E :
  (false, false) \in char 1 E -> exists x, E = [set x].
Proof.
move/mem_charP => [x [xinE /char0P downE /char0P upE]].
exists x; apply clsetP => y.
rewrite [RHS](reflect_eq eqP) eq_sym -[LHS]in_setE; apply prop_congr.
case: (ltgtP x y) => [ltxy|ltyx|<- //].
- apply/negP => yinP; apply upE; exists y.
  by rewrite in_setE /up /setI -[E y]in_setE yinP ltxy.
- apply/negP => yinP; apply downE; exists y.
  by rewrite in_setE /down /setI -[E y]in_setE yinP ltyx.
Qed.

Lemma charFFE P :
  (false, false) \in char 1 P -> char 1 P = [set (false, false)]%SET.
Proof. by move/charFF => [x ->]; apply char1pred1. Qed.

End Def.

Lemma char0nat : char 0 (@setT nat) = true.
Proof. by apply/char0P; exists 0; rewrite in_setE /setT. Qed.

Lemma char1nat : char 1 (@setT nat) = [set (false, true); (true, true)]%SET.
Proof.
apply/setP => [] [[|] [|]]; rewrite in_set2 ?eqE /= ?eqE /= ?/eqb /=.
- apply/(mem_charP (n := 0)) => /=.
  exists 1%N; rewrite in_setE {1}/setT.
  split => //; apply/char0P => /=.
  + by exists 0; rewrite in_setE /down /up /setI.
  + by exists 2; rewrite in_setE /down /up /setI.
- apply/negP => /(mem_charP (n := 0)) /= [x [_ _ /char0P]] /=; apply.
  by exists x.+1; rewrite in_setE /down /up /setI ltEnat.
- apply/(mem_charP (n := 0)) => /=.
  exists 0%N; rewrite in_setE {1}/setT.
  split => //; apply/char0P => /=.
  + by move=> [x]; rewrite in_setE /down /up /setI ltEnat => [] [].
  + by exists 1%N; rewrite in_setE /down /up /setI ltEnat.
- apply/negP => /(mem_charP (n := 0)) /= [x [_ _ /char0P]] /=; apply.
  by exists x.+1; rewrite in_setE /down /up /setI ltEnat.
Qed.

