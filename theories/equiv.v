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
From mathcomp Require Import boolp classical_sets.

Require Import order.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.
Open Scope order_scope.

Notation down x := [orderType of [subType of {y | y < x}]].
Notation up x := [orderType of [subType of {y | y > x}]].

Section Def.

Section Empty.

Variable (u : unit) (X : orderType u).
Definition is_not_empty : bool := `[<exists x : X, true>].

Lemma is_not_emptyP: reflect (exists x : X, True) is_not_empty.
Proof.
apply (iffP (exists_asboolP _)) => [][a] _; exists a => //.
exact/asboolP.
Qed.

Lemma is_not_emptyX (x : X) : is_not_empty.
Proof. by apply/is_not_emptyP; exists x. Qed.

Lemma is_emptyX : (X -> False) -> is_not_empty = false.
Proof. by rewrite /is_not_empty => notX; apply/is_not_emptyP => [][] /notX. Qed.

End Empty.


Fixpoint nth_char_type (n : nat) : finType :=
  if n is n'.+1 then
     [finType of {set (nth_char_type n') * (nth_char_type n')}]
  else [finType of bool].

Fixpoint nth_char_rec (n : nat) (u : unit) (X : orderType u) :
  nth_char_type n :=
  if n is n'.+1 then
    [set Cpair |
     `[<exists x : X, (nth_char_rec n' (down x),
                       nth_char_rec n' (up x)) = Cpair >]]
  else
    (is_not_empty X : nth_char_type 0).

Definition nth_char (n : nat) (u : unit) (X : orderType u) of phant X :=
  nth_char_rec n X.

End Def.

Notation char n X := (@nth_char n _ _ (Phant X)).

Section Reflect.

Variable (n : nat) (u : unit) (X : orderType u).

Lemma mem_nth_char l r :
  reflect
    (exists2 x : X, char n (down x) = l & char n (up x) = r)
    ((l, r) \in char n.+1 X).
Proof.
rewrite /nth_char /= inE; apply (iffP (exists_asboolP _)) => [][a].
- by move/asboolP => [<- <-]; exists a.
- by move=> <- <-; exists a; apply/asboolP.
Qed.

End Reflect.

Lemma char0nat : char 0 nat = true.
Proof. by apply/is_not_emptyP; exists 0. Qed.

Lemma char1nat : char 1 nat = [set (false, true); (true, true)].
Proof.
apply/setP => [] [[|] [|]]; rewrite in_set2 ?eqE /= ?eqE /= ?/eqb /=.
- apply/(@mem_nth_char 0) => /=.
  exists 1%N; apply/is_not_emptyP => /=.
  + have lt01 : 0%N < 1%N by rewrite ltEnat.
    by exists (exist (fun x => x < 1%N) 0 lt01).
  + have lt12 : 1%N < 2%N by rewrite ltEnat.
    by exists (exist (fun x => 1%N < x) 2 lt12).
- apply/negP => /(@mem_nth_char 0) [/= x _].
  move/is_not_emptyP; apply.
  have ltx1 : x%N < x.+1%N by rewrite ltEnat.
  by exists (exist (fun y => x < y) x.+1 ltx1).
- apply/(@mem_nth_char 0) => /=.
  exists 0%N; apply/is_not_emptyP => /=.
  + by move=> [] [y].
  + have lt01 : 0%N < 1%N by rewrite ltEnat.
    by exists (exist (fun x => 0 < x) 1%N lt01).
- apply/negP => /(@mem_nth_char 0) [/= x _].
  move/is_not_emptyP; apply.
  have ltx1 : x%N < x.+1%N by rewrite ltEnat.
  by exists (exist (fun y => x < y) x.+1 ltx1).
Qed.


