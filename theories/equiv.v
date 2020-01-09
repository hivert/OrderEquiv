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


Section Bla.

Notation down x := [orderType of [subType of {y | y < x}]].
Notation up x := [orderType of [subType of {y | y > x}]].

Definition is_not_empty (u : unit) (X : orderType u) : bool :=
  `[<exists x : X, true>].


Fixpoint nth_char_type (n : nat) : Type :=
  if n is n'.+1 then
     (nth_char_type n') * (nth_char_type n') -> bool
  else bool.

Fixpoint nth_char (n : nat) (u : unit) (X : orderType u) :
  nth_char_type n :=
  if n is n'.+1 then
    fun Cpair => `[<exists x : X,
                      nth_char n' (down x) = Cpair.1 /\
                      nth_char n' (up x)   = Cpair.2 >]
  else
    (is_not_empty X : nth_char_type 0).

Lemma char0nat : nth_char 0 [orderType of nat] = true.
Proof.
rewrite /= /is_not_empty; apply/exists_asboolP; exists 0.
by apply/asboolP.
Qed.

Lemma char1nat :
  nth_char 1 [orderType of nat] =
  fun bp =>
    match bp with
      (false, true) | (true, true) => true
    | _ => false
    end.
Proof.
apply funext => [] [[|] [|]] /=; apply/exists_asboolP.
- exists 1%N.
  apply/asboolP; split; rewrite /= /is_not_empty; apply/exists_asboolP.
  + rewrite /=.
    have lt01 : 0%N < 1%N by rewrite ltEnat.
    exists (exist (fun x => x < 1%N) 0 lt01).
    by apply/asboolP.
  + rewrite /=.
    have lt12 : 1%N < 2%N by rewrite ltEnat.
    exists (exist (fun x => 1%N < x) 2 lt12).
    by apply/asboolP.
- move=> [x0] /asboolP [_].
  rewrite /is_not_empty.
  have ltx0 : x0%N < x0.+1%N by rewrite ltEnat.
  move/negP; apply.
  apply/exists_asboolP.
  exists (exist (fun x => x0 < x) x0.+1 ltx0).
  by apply/asboolP.
- exists 0%N.
  apply/asboolP; split; rewrite /= /is_not_empty; apply/exists_asboolP.
  + apply/exists_asboolP; apply/negP => /asboolP [].
    move=> [y].
    by rewrite ltEnat.
  + rewrite /=.
    have lt01 : 0%N < 1%N by rewrite ltEnat.
    exists (exist (fun x => 0%N < x) 1%N lt01).
    by apply/asboolP.
- move=> [x0] /asboolP [_].
  rewrite /is_not_empty.
  have ltx0 : x0%N < x0.+1%N by rewrite ltEnat.
  move/negP; apply.
  apply/exists_asboolP.
  exists (exist (fun x => x0 < x) x0.+1 ltx0).
  by apply/asboolP.
Qed.

End Bla.
