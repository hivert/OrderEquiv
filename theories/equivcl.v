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
From mathcomp Require Import boolp classical_sets.

Require Import order.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.

Open Scope order_scope.
Open Scope classical_set_scope.

Lemma setP X (E F : set X) : (E =1 F) <-> (E = F).
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

Fixpoint char_type n : Type :=
  if n is n'.+1 then set (char_type n' * char_type n') else bool.

Fixpoint char_rec n E : char_type n :=
  if n is n'.+1 then
    [set (char_rec n' (down E x), char_rec n' (up E x)) | x in E]
  else `[exists x, x \in E].
Definition char n P := nosimpl (char_rec n P).

Lemma char0P E : reflect (exists x, x \in E) (char 0 E).
Proof. exact/existsbP. Qed.

Lemma mem_charP n E l r :
  reflect
    (exists x : X, [/\ x \in E, char n (down E x) = l & char n (up E x) = r])
    ((l, r) \in char n.+1 E).
Proof.
apply (iffP idP); rewrite /char /= inE.
- by move/asboolP => [x xinE [<- <-]]; exists x; rewrite in_setE.
- by move=> [x [xinP <- <-]]; apply/asboolP; exists x; rewrite // -in_setE.
Qed.

Lemma char0_pred0 : char 0 set0 = false.
Proof. by apply/char0P => [] [x]; rewrite in_setE /set0. Qed.
Lemma char0_true P : char 0 P -> P <> set0.
Proof.
move/char0P => [x xinP eqP0].
by move: xinP; rewrite eqP0 in_setE /set0.
Qed.

Lemma char1_pred0 : char 1 set0 = set0.
Proof.
rewrite -subset0 => [[l r]].
rewrite {2}/set0 -in_setE =>/mem_charP [x []].
by rewrite in_setE.
Qed.

Lemma char10P E : char 1 E = set0 -> E = set0.
Proof.
move=> ch1; rewrite -subset0 => x /=.
rewrite /set0 => Ex.
suff : (char 0 (down E x), char 0 (up E x)) \in char 1 E.
  by rewrite ch1 in_setE.
by apply/mem_charP; exists x; rewrite in_setE.
Qed.

Lemma char1pred1 x0 : char 1 [set x0] = [set (false, false)].
Proof.
rewrite -setP => [[a b]].
rewrite -[in LHS]in_setE [RHS](reflect_eq eqP); apply prop_congr.
rewrite !eqE /= !eqE /= /eqb /= !addbF -negb_or.
case: a => /=.
  apply/negP => /mem_charP [x []].
  rewrite in_setE {1}/set1 => ->{x}.
  by rewrite down1 char0_pred0.
case: b => /=.
- apply/negP => /mem_charP [x []].
  rewrite in_setE {1}/set1 => ->{x}.
  by rewrite up1 char0_pred0.
- apply/mem_charP; exists x0.
  by rewrite in_setE {1}/set1 down1 up1 char0_pred0.
Qed.

Lemma charFF E :
  (false, false) \in char 1 E -> exists x, E = [set x].
Proof.
move/mem_charP => [x [xinE /char0P downE /char0P upE]].
exists x; apply setP => y.
rewrite [RHS](reflect_eq eqP) eq_sym -[LHS]in_setE; apply prop_congr.
case: (ltgtP x y) => [ltxy|ltyx|<- //].
- apply/negP => yinP; apply upE; exists y.
  by rewrite in_setE /up /setI -[E y]in_setE yinP ltxy.
- apply/negP => yinP; apply downE; exists y.
  by rewrite in_setE /down /setI -[E y]in_setE yinP ltyx.
Qed.

Lemma charFFE P :
  (false, false) \in char 1 P -> char 1 P = [set (false, false)].
Proof. by move/charFF => [x ->]; apply char1pred1. Qed.

End Def.

Lemma char0nat : char 0 (@setT nat) = true.
Proof. by apply/char0P; exists 0; rewrite in_setE /setT. Qed.

Lemma char1nat : char 1 (@setT nat) = [set (false, true); (true, true)].
Proof.
rewrite -setP => [[a b]].
rewrite -[in LHS]in_setE.
rewrite [RHS]/setU /set1 !(reflect_eq eqP) (reflect_eq orP).
apply/eqP/prop_congr.
rewrite !eqE /= !eqE /= /eqb /= !addbT !addbF !negbK -andb_orl orNb /=.
case: a b => [|] [|].
- apply/mem_charP => /=; exists 1%N.
  rewrite in_setE {1}/setT; split => //; apply/char0P => /=.
  + by exists 0; rewrite in_setE /down /up /setI.
  + by exists 2; rewrite in_setE /down /up /setI.
- apply/negP => /(mem_charP (n := 0)) /= [x [_ _ /char0P]] /=; apply.
  by exists x.+1; rewrite in_setE /down /up /setI ltEnat.
- apply/mem_charP => /=; exists 0%N.
  rewrite in_setE {1}/setT; split => //; apply/char0P => /=.
  + by move=> [x]; rewrite in_setE /down /up /setI ltEnat => [] [].
  + by exists 1%N; rewrite in_setE /down /up /setI ltEnat.
- apply/negP => /mem_charP /= [x [_ _ /char0P]] /=; apply.
  by exists x.+1; rewrite in_setE /down /up /setI ltEnat.
Qed.

