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
From mathcomp Require Import ssralg ssrnum ssrint.

Require Import order.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Syntax.
Import Order.TTheory.
Open Scope order_scope.



Definition bool_simp := (addbF, addbT, andbT, andbF, orbT, orbF).

Lemma predext (T : Type) (p1 p2 : simpl_pred T) : p1 = p2 <-> p1 =i p2.
Proof.
split => [-> x // | eqf].
case: p1 p2 eqf => [p1] [p2] eqf; suff -> : p1 = p2 by [].
by apply funext => x; have:= eqf x; rewrite !unfold_in /=.
Qed.



Section CanonicalEnumeration.

Definition enumft (T : finType) : seq T :=
  match T as t return (seq t) with
    @Finite.Pack T class => Finite.mixin_enum class
  end.

Lemma enumftE (T : finType) : enum T = enumft T.
Proof.
rewrite enumT unlock /enumft.
by case: T => /= T [] /= base [] /=.
Qed.

Lemma enum_bool : enum [finType of bool] = [:: true; false].
Proof. by rewrite enumftE. Qed.

(* Not used -- doesn't scale further *)
Lemma enum_bool_bool :
  enum [finType of bool * bool] =
  [:: (true, true); (true, false); (false, true); (false, false)].
Proof. by rewrite enumftE /= /prod_enum enum_bool. Qed.


Variable (T : finType).
Implicit Type (en : seq T) (s : {set T}).

Lemma eq_finset_enum (s1 s2 : {set T}) :
  (s1 == s2) = all (fun pr => (pr \in s1) == (pr \in s2)) (enum T).
Proof.
apply/eqP/allP => [-> // | Heq]; apply/setP => t; apply/eqP/Heq.
by rewrite mem_enum.
Qed.

Fixpoint subset_of_seq en : seq {set T} :=
  if en is x :: en' then
    let srec := subset_of_seq en' in
    srec ++ [seq (x |: sr) | sr <- srec]
  else [:: set0].

Lemma mem_subset_of_seqE en s x :
  s \in subset_of_seq en -> x \in s -> x \in en.
Proof.
elim: en s x => [|e0 en IHen] s x /=.
  by rewrite !inE => /eqP ->; rewrite inE.
rewrite mem_cat !inE => /orP [{}/IHen H/H ->|]; first by rewrite orbT.
move/mapP => /=[s' {}/IHen ins ->{s}].
by rewrite !inE => /orP [/eqP-> | /ins->]; rewrite ?eqxx ?orbT.
Qed.

Lemma subset_of_seq_uniq en : uniq en -> uniq (subset_of_seq en).
Proof.
elim: en => [|x en IHen]//= /andP [xinen uniqen].
rewrite cat_uniq IHen //=; apply/andP; split.
- apply/hasP => [/=[s0 /mapP [/= s sin ->{s0}]]] /mem_subset_of_seqE.
  by move/(_ x) => Habs; move: xinen; rewrite {}Habs // !inE eqxx.
- rewrite map_inj_in_uniq ?IHen // => /= s t.
  move=> /mem_subset_of_seqE mems /mem_subset_of_seqE memt Heq.
  have /setU1K <- : x \notin s by apply/contra/mems: xinen.
  rewrite Heq setU1K //.
  by apply/contra/memt: xinen.
Qed.

Lemma subset_of_seqP en s : {subset s <= en} -> s \in subset_of_seq en.
Proof.
elim: en s => [|x en IHen] s subs /=.
  by rewrite inE; apply/set0Pn => [[x {}/subs]]; rewrite in_nil.
rewrite mem_cat; apply/orP.
case: (boolP (x \in s)) => [xin | xnotin].
- right; apply/mapP; exists (s :\ x); last by rewrite setD1K.
  apply: IHen => x0; rewrite !inE => /andP [neqx {}/subs].
  by rewrite !inE => /orP[]//; apply/contraLR.
- left; apply: IHen => x0 x0in.
  move/(_ _ x0in): subs; rewrite inE.
  suff /negbTE -> : x0 != x by [].
  by apply/contra: xnotin => /eqP <-.
Qed.

Definition enum_set := subset_of_seq (enum T).

Lemma enum_finset : perm_eq (enum {set T}) enum_set.
Proof.
apply uniq_perm.
- exact: enum_uniq.
- exact/subset_of_seq_uniq/enum_uniq.
- move=> /= s; apply: esym; rewrite mem_enum inE /enum_set.
  by apply: subset_of_seqP => x _; rewrite mem_enum inE.
Qed.

End CanonicalEnumeration.


(*
Lemma bla : subset_of_seq (enum_set [finType of bool * bool]) = [::].
Proof.
rewrite [subset_of_seq]lock.
rewrite /enum_set enum_bool_bool /= !setU0 !setUA.
rewrite -lock /=.
*)

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

Lemma down_sub P x : {subset down P x <= P}.
Proof. by move=> y; rewrite !inE => /andP[]. Qed.
Lemma up_sub P x : {subset up P x <= P}.
Proof. by move=> y; rewrite !inE => /andP[]. Qed.

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


Fixpoint ordchar_type n : finType :=
  if n is n'.+1 then
     [finType of {set (ordchar_type n') * (ordchar_type n')}]
  else [finType of bool].

Fixpoint ordchar_rec n P : ordchar_type n :=
  if n is n'.+1 then
    [set Cpair |
     `[exists x in P, (ordchar_rec n' (down P x),
                       ordchar_rec n' (up P x)) == Cpair ]]
  else `[exists x, x \in P].
Definition ordchar n P := nosimpl (ordchar_rec n P).

Lemma ordchar0P P : reflect (exists x, x \in P) (ordchar 0 P).
Proof. exact/existsbP. Qed.

Lemma mem_ordcharP n P l r :
  reflect
    (exists x, [/\ x \in P, ordchar n (down P x) = l & ordchar n (up P x) = r])
    ((l, r) \in ordchar n.+1 P).
Proof.
apply (iffP idP); rewrite /ordchar /= inE.
- by move/existsbP => [x /andP [xinP /eqP [<- <-]]]; exists x.
- move=> [x [xinP <- <-]]; apply/existsbP; exists x.
  exact/andP.
Qed.

Lemma ordchar0_pred0 : ordchar 0 pred0 = false.
Proof. by apply/ordchar0P => [] [x]; rewrite inE. Qed.
Lemma ordchar0_true P : ordchar 0 P -> P <> pred0.
Proof.
move/ordchar0P => [x xinP eqP0].
by move: xinP; rewrite eqP0 inE.
Qed.

Lemma ordchar_pred0 n : ordchar n.+1 pred0 = set0.
Proof.
apply/setP => [[l r]]; rewrite [RHS]inE.
apply/negP => /(mem_ordcharP (n := n)) [x []].
by rewrite inE.
Qed.

(* James's 6-th lemma *)
Lemma ordchar1_eq0P P : ordchar 1 P = set0 -> P = pred0.
Proof.
move=> ch1; apply funext => x /=.
apply/negP => Px.
suff : (ordchar 0 (down P x), ordchar 0 (up P x)) \in ordchar 1 P.
  by rewrite ch1 inE.
by apply/mem_ordcharP; exists x.
Qed.

Lemma ordchar1_pred1 x0 : ordchar 1 (pred1 x0) = [set (false, false)].
Proof.
apply/setP => [] [[|] /= b]; rewrite in_set1 ?eqE /=.
  apply/negP => /(mem_ordcharP (n := 0)) /= [x []].
  rewrite inE => /eqP ->{x}.
  by rewrite down_pred1 ordchar0_pred0.
case: b; rewrite eqE /= /eqb /=.
- apply/negP => /(mem_ordcharP (n := 0)) /= [x []].
  rewrite inE => /eqP ->{x} _.
  by rewrite up_pred1 ordchar0_pred0.
- apply/(mem_ordcharP (n := 0)); exists x0.
  by rewrite inE down_pred1 up_pred1 ordchar0_pred0.
Qed.

(* James's 7-th lemma *)
Lemma ordcharFF P :
  (false, false) \in ordchar 1 P -> exists x, P = pred1 x.
Proof.
move/mem_ordcharP => [x [xinP /ordchar0P downP /ordchar0P upP]].
exists x; apply funext => y.
rewrite [RHS]inE /= eq_sym.
have /= -> := (topredE y P).
case: (ltgtP x y) => [ltxy|ltyx|<- //].
- apply/negP => yinP; apply upP; exists y.
  by rewrite !inE yinP ltxy.
- apply/negP => yinP; apply downP; exists y.
  by rewrite !inE yinP ltyx.
Qed.

Lemma ordcharFFE P :
  (false, false) \in ordchar 1 P -> ordchar 1 P = [set (false, false)].
Proof. by move/ordcharFF => [x ->]; apply ordchar1_pred1. Qed.

Lemma up_down P x y :
  x \in P -> y \in P -> (y \in up P x) = (x \in down P y).
Proof. by rewrite !inE => -> ->. Qed.

(* James's 5-th lemma *)
Lemma ordcharFT P :
  (false, true) \in ordchar 1 P ->
  (true, true) \in ordchar 1 P \/ (true, false) \in ordchar 1 P.
Proof.
move/mem_ordcharP => [x0 [x0inP /ordchar0P downP /ordchar0P [x1 /upP[x1inP lt01]]]].
case: (boolP ((true, true) \in ordchar 1 P)) => Htt; [left | right] => //.
apply/mem_ordcharP; exists x1; split; first by [].
- apply/ordchar0P; exists x0.
  by rewrite -up_down //; apply/upP.
- apply/ordchar0P => [] [x2 /upP [x2inP lt12]].
  move: Htt => /negP; apply; apply/mem_ordcharP.
  exists x1; split => //; apply/ordchar0P.
  + by exists x0; apply/upP.
  + by exists x2; apply/upP.
Qed.

End Def.


Section Dual.

Variable (u : unit) (Ord : orderType u).
Implicit Type (x t : Ord) (P : pred Ord).

Local Arguments ordchar {u} Ord.
Local Arguments down {u} Ord.
Local Arguments up {u} Ord.

Let OrdC := [orderType of Ord^d].


Lemma down_dual P x : down OrdC P x = up Ord P x.
Proof. by apply predext => y; rewrite !inE. Qed.
Lemma up_dual P x : up OrdC P x = down Ord P x.
Proof. by apply predext => y; rewrite !inE. Qed.


Fixpoint rev_ordchar n : ordchar_type n -> ordchar_type n :=
  if n is n'.+1 then
    fun ch => [set (rev_ordchar C.2, rev_ordchar C.1) | C in ch]
  else id.

Lemma rev_ordcharK n : involutive (@rev_ordchar n).
Proof.
elim: n => [|n IHn] P //=.
rewrite -imset_comp; apply/setP => [[chdown chup]] /=.
set f := (F in imset F _).
suff {chdown chup P} : f =1 id by move/eq_imset => ->; rewrite imset_id.
rewrite {}/f => [[chdown chup]] /=.
by rewrite !IHn.
Qed.

Lemma mem_rev_ordchar n ch1 ch2 (ch : ordchar_type n.+1) :
  ((ch1, ch2) \in rev_ordchar ch) = ((rev_ordchar ch2, rev_ordchar ch1) \in ch).
Proof.
rewrite /=; apply/imsetP/idP => [[[c1 c2] /= cin [-> ->]] | rchin].
  by rewrite !rev_ordcharK.
by exists (rev_ordchar ch2, rev_ordchar ch1); rewrite ?rev_ordcharK.
Qed.

Lemma mem_rev_ordchar1 (ch1 ch2 : bool) (ch : ordchar_type 1) :
  ((ch1, ch2) \in rev_ordchar ch) = ((ch2, ch1) \in ch).
Proof. by rewrite [LHS]mem_rev_ordchar. Qed.

Lemma ordchar0_dual P : ordchar Ord 0 P = ordchar OrdC 0 P.
Proof. by apply/ordchar0P/ordchar0P => [] [x xinP]; exists x. Qed.

Lemma ordchar_dual n P : rev_ordchar (ordchar OrdC n P) = ordchar Ord n P.
Proof.
elim: n P => [|n IHn] P /=; first exact: ordchar0_dual.
apply/setP => /= [[chdown chup]].
apply/imsetP/mem_ordcharP => /= [ [[chd chu]] | [x [xinP dE uE]]].
- move=> /mem_ordcharP [x [xinP <-{chd} <-{chu}]] [->{chdown} ->{chup}].
  by exists x; rewrite -!IHn ?downdual ?updual.
- exists (rev_ordchar chup, rev_ordchar chdown).
  + apply/mem_ordcharP => /=.
    by exists x; split; rewrite // -?uE -?dE -IHn !rev_ordcharK ?downdual ?updual.
  + by rewrite /= !rev_ordcharK.
Qed.

End Dual.


Section Isomorphism.

Variables (u : unit) (E : orderType u).
Variables (v : unit) (F : orderType v) .
Implicit Type (P : pred E) (Q : pred F) (f : E -> F).

Definition impred (f : E -> F) (P : pred E) y :=
  `[exists x, (x \in P) && (f x == y)].
Lemma impredP P f y :
  reflect (exists2 x, x \in P & f x = y) (impred f P y).
Proof.
rewrite /impred; apply (iffP (existsbP _)) => [] [x].
- by move=> /andP [xin /eqP feq]; exists x.
- by move=> xin /eqP feq; exists x; rewrite xin feq.
Qed.

Lemma in_impred f P x : x \in P -> f x \in impred f P.
Proof. by move=> xin; apply/impredP; exists x. Qed.

Definition is_isom P Q f :=
  [/\
   {in P &, injective f},
   impred f P = Q &
   {in P &, {homo f : x y / x < y}}
  ].

Section IsomTheory.

Variables (P : pred E) (Q : pred F) (f : E -> F).
Hypothesis (isom_f : is_isom P Q f).

Lemma isom_can : {in P &, forall x y, f x < f y -> x < y}.
Proof.
move: isom_f => [bif imf morf] x y xin yin ltfxy.
case: (ltgtP x y) => // [ltyx | eqxy].
- by rewrite -(lt_asym (f x) (f y)) ltfxy /= morf.
- by move: ltfxy; rewrite eqxy ltxx.
Qed.

Lemma isom_impred_down x : x \in P -> impred f (down P x) = down Q (f x).
Proof.
move=> xin.
have:= isom_f => [] [bif <- morf]; apply funext => y.
rewrite !inE; apply/impredP/andP => [[x1]|[yin lty]].
- rewrite !inE => /andP [x1in ltx1 <-{y}].
  by split; [exact: in_impred | exact: morf].
- move/impredP: yin => [x1 x1in eqy].
  exists x1; rewrite // !inE x1in /=.
  by move: lty; rewrite -{}eqy => /isom_can; apply.
Qed.
Lemma isom_down x : x \in P -> is_isom (down P x) (down Q (f x)) f.
Proof.
move: isom_f => [finj imf morf].
move=> xin; split.
- exact/(sub_in2 _ finj)/down_sub.
- apply funext => y; apply/impredP/andP; rewrite !inE.
  + move=> [x1]; rewrite !inE => /andP[x1in ltx1 <-{y}].
    by rewrite -imf; split; [exact: in_impred | exact: morf].
  + rewrite -imf => [[/impredP [x0 x0in <-{y}]]].
    move=> /(isom_can x0in xin) ltx0x.
    by exists x0 => //; rewrite !inE x0in ltx0x.
- exact/(sub_in2 _ morf)/down_sub.
Qed.

Lemma isom_impred_up x : x \in P -> impred f (up P x) = up Q (f x).
Proof.
have:= isom_f => [] [bif <- morf] xin; apply funext => y.
rewrite !inE; apply/impredP/andP => [[x1]|[yin lty]].
- rewrite !inE => /andP [x1in ltx1 <-{y}].
  by split; [exact: in_impred | exact: morf].
- move/impredP: yin => [x1 x1in eqy].
  exists x1; rewrite // !inE x1in /=.
  by move: lty; rewrite -{}eqy => /isom_can; apply.
Qed.
Lemma isom_up x : x \in P -> is_isom (up P x) (up Q (f x)) f.
Proof.
move: isom_f => [finj imf morf] xin; split.
- exact/(sub_in2 _ finj)/up_sub.
- apply funext => y; apply/impredP/andP; rewrite !inE.
  + move=> [x1]; rewrite !inE => /andP[x1in ltx1 <-{y}].
    by rewrite -imf; split; [exact: in_impred | exact: morf].
  + rewrite -imf => [[/impredP [x0 x0in <-{y}]]].
    move=> /(isom_can xin x0in) ltx0x.
    by exists x0 => //; rewrite !inE x0in ltx0x.
- exact/(sub_in2 _ morf)/up_sub.
Qed.

End IsomTheory.

Variables (P : pred E) (Q : pred F) (f : E -> F).
Hypothesis (isom_f : is_isom P Q f).

Lemma ordchar_isom n : ordchar n P = ordchar n Q.
Proof.
elim: n P Q isom_f => [|n IHn] /= PP QQ isof.
  move: isof => [bif imf morf].
  apply/ordchar0P/ordchar0P => [[x xin] | [y]].
  + by rewrite -imf; exists (f x); apply: in_impred.
  + by rewrite -imf => /impredP [x xin_]; exists x.
apply/setP => [[chu chd]].
have:= isof => [[bif imf morf]].
apply/mem_ordcharP/mem_ordcharP => [[x [xin]] | [y [yin]]] <- <-.
- exists (f x); split.
  + by rewrite -imf; apply: in_impred.
  + exact/esym/IHn/isom_down.
  + exact/esym/IHn/isom_up.
- move: yin; rewrite -imf => /impredP [x xin <-{y}].
  exists x; rewrite imf.
  split => //; apply IHn; [exact: isom_down | exact: isom_up].
Qed.

End Isomorphism.


Section IsomDual.

Variables (u : unit) (E : orderType u).
Variables (v : unit) (F : orderType v).

Lemma isom_dual P Q (f : E -> F) :
  is_isom (E := E) (F := F) P Q f ->
  is_isom (E := [orderType of E^d]) (F := [orderType of F^d]) P Q f.
Proof.
move=> [finj imf morf]; split => // x y xinP yinP.
by rewrite !ltEdual; apply morf.
Qed.

End IsomDual.


Section OrdcharPredicate.

Variables (u : unit) (Ord : orderType u).
Implicit Types (P : pred Ord) (ch : ordchar_type 1).

Lemma ordcharTF P :
  (true, false) \in ordchar 1 P ->
  (true, true) \in ordchar 1 P \/ (false, true) \in ordchar 1 P.
Proof. by rewrite -(ordchar_dual 1 P) !mem_rev_ordchar1; apply: ordcharFT. Qed.

Definition is_ordchar1 :=
  [pred ch : ordchar_type 1 | [&&
   (((false, false) \in ch) ==> (ch == [set (false, false)])),
   (((true, false) \in ch) ==>
    (((true, true) \in ch) || ((false, true) \in ch))) &
   (((false, true) \in ch) ==>
    (((true, true) \in ch) || ((true, false) \in ch)))
  ]].

Lemma is_ordchar1P P : is_ordchar1 (ordchar 1 P).
Proof.
apply/and3P; split; apply/implyP.
- by move/ordcharFFE ->.
- by move/ordcharTF => [] -> //; rewrite orbT.
- by move/ordcharFT => [] -> //; rewrite orbT.
Qed.

End OrdcharPredicate.



(*******************************************)
(* Various examples for the classification *)

Lemma ordchar0_nat : ordchar 0 (@predT nat) = true.
Proof. by apply/ordchar0P; exists 0. Qed.
Lemma ordchar0_nat_dual : ordchar 0 (@predT nat^d) = true.
Proof. by apply/ordchar0P; exists 0. Qed.

Lemma ordchar1_nat : ordchar 1 (@predT nat) = [set (false, true); (true, true)].
Proof.
apply/setP => [] [[|] [|]]; rewrite in_set2 ?eqE /= ?eqE /= ?/eqb /=.
- apply/(mem_ordcharP (n := 0)) => /=.
  exists 1%N; split => //; apply/ordchar0P => /=.
  + by exists 0.
  + by exists 2.
- apply/negP => /(mem_ordcharP (n := 0)) /= [x [_ _ /ordchar0P]] /=; apply.
  by exists x.+1; rewrite !inE ltEnat /=.
- apply/(mem_ordcharP (n := 0)) => /=.
  exists 0%N; split => //; apply/ordchar0P => /=.
  + by move=> [].
  + by exists 1%N.
- apply/negP => /(mem_ordcharP (n := 0)) /= [x [_ _ /ordchar0P]] /=; apply.
  by exists x.+1; rewrite !inE ltEnat /=.
Qed.

Lemma isom_up_nat (n : nat) :
  is_isom (@predT nat) (up predT n) (fun i => i + n.+1).
Proof.
split => /=.
- apply: (in2W (can_inj (addnK _))).
- apply funext => i; rewrite !inE /=.
  apply/impredP/idP => [[/= m _ <-] | ltni].
  + by rewrite ltEnat addnS ltnS leq_addl.
  + by exists (i - n.+1); rewrite // subnK.
- by move=> i j _ _; rewrite !ltEnat ltn_add2r.
Qed.

Lemma ordchar1_up_nat (n : nat) :
  ordchar 1 (up predT n) = [set (false, true); (true, true)].
Proof.
rewrite -ordchar1_nat; apply esym.
exact/ordchar_isom/isom_up_nat.
Qed.


Lemma ordchar1_nat_dual :
  ordchar 1 (@predT nat^d) = [set (true, false); (true, true)].
Proof.
by rewrite -[LHS]rev_ordcharK ordchar_dual ordchar1_nat /= imsetU1 imset_set1.
Qed.


Lemma ordchar0_down2 : ordchar 0 (down predT 2) = true.
Proof. by apply/ordchar0P; exists 0. Qed.

Lemma ordchar1_down2 :
  ordchar 1 (down predT 2) = [set (false, true); (true, false)].
Proof.
apply/setP => [] [[|] [|]]; rewrite in_set2 ?eqE /= ?eqE /= ?/eqb /=.
- apply/negP => /(mem_ordcharP (n := 0)) /= [] [|[|i]];
                  rewrite //= inE => [] [] // _.
  + by move=> /ordchar0P/= [x]; rewrite !inE => /andP [].
  + move=> _ /ordchar0P/= [x]; rewrite !inE => /andP [].
    by rewrite !ltEnat ltnS => /leq_ltn_trans {}H/H; rewrite ltnn.
- apply/(mem_ordcharP (n := 0)) => /=.
  exists 1%N; split => //; apply/ordchar0P => /=.
  + by exists 0.
  + move=> [x]; rewrite !inE => /andP [].
    by rewrite !ltEnat ltnS => /leq_ltn_trans {}H/H; rewrite ltnn.
- apply/(mem_ordcharP (n := 0)) => /=.
  exists 0%N; split => //; apply/ordchar0P => /=.
  + by move=> [x]; rewrite !inE => /andP [].
  + by exists 1%N.
- apply/negP => /(mem_ordcharP (n := 0)) /= [] [|[|i]];
                  rewrite //= inE => [] [] // _.
  + by move=> _ /ordchar0P/= H; apply: H; exists 1%N.
  + by move=> /ordchar0P/= H _; apply: H; exists 0%N.
Qed.


Lemma ordchar0_down3plus n : ordchar 0 (down predT n.+3) = true.
Proof. by apply/ordchar0P; exists 0. Qed.
Lemma ordchar0_down3 : ordchar 0 (down predT 3) = true.
Proof. exact: ordchar0_down3plus. Qed.

Lemma ordchar1_down3plus n :
  ordchar 1 (down predT n.+3) = [set (false, true); (true, true); (true, false)].
Proof.
apply/setP => [] [[|] [|]]; rewrite ![in RHS]inE ?eqE /= ?eqE /= ?/eqb /=.
- apply/(mem_ordcharP (n := 0)) => /=.
  exists 1%N; split => //; apply/ordchar0P => /=.
  + by exists 0.
  + by exists 2.
- apply/(mem_ordcharP (n := 0)) => /=.
  exists n.+2; split.
  + by rewrite !inE //= ltEnat !ltnS.
  + by apply/ordchar0P => /=; exists 0.
  + apply/ordchar0P => /=[][x]; rewrite !inE => /andP [].
    by rewrite !ltEnat ltnS => /leq_ltn_trans {}H/H; rewrite ltnn.
- apply/(mem_ordcharP (n := 0)) => /=.
  exists 0%N; split => //; apply/ordchar0P => /=.
  + by move=> [x]; rewrite !inE => /andP [].
  + by exists 1%N.
- apply/negP => /(mem_ordcharP (n := 0)) /= [] [|[|i]];
                  rewrite //= inE => [] [] // _.
  + by move=> _ /ordchar0P/= H; apply: H; exists 1%N.
  + by move=> /ordchar0P/= H _; apply: H; exists 0%N.
  + by move=> /ordchar0P/= H _; apply: H; exists 0%N.
Qed.
Lemma ordchar1_down3 :
  ordchar 1 (down predT 3) = [set (false, true); (true, true); (true, false)].
Proof. exact: ordchar1_down3plus. Qed.



Section NumOrdered.

Variable (T : realDomainType).

Import Num.Theory.

Program Definition realDomOrderMixin :=
  @LeOrderMixin T Num.Def.ler Num.Def.ltr Num.min Num.max _ _ _ _ _ _.
Next Obligation. by rewrite ltr_def. Qed.
Next Obligation. exact: ler_anti. Qed.
Next Obligation. exact: ler_trans. Qed.
Next Obligation. exact: ler_total. Qed.

Canonical realDom_porderType := POrderType total_display T realDomOrderMixin.
Canonical realDom_distrLatticeType := DistrLatticeType T realDomOrderMixin.
Canonical realDom_orderType := OrderType T realDomOrderMixin.

Lemma leRealDomE (x y : T) : (x <= y)%O = (x <= y)%R.
Proof. by []. Qed.
Lemma ltRealDomE (x y : T) : (x < y)%O = (x < y)%R.
Proof. by []. Qed.

End NumOrdered.

Definition int_orderMixin := realDomOrderMixin [realDomainType of int].
Canonical int_porderType := POrderType total_display int int_orderMixin.
Canonical int_distrLatticeType := DistrLatticeType int int_orderMixin.
Canonical int_orderType := OrderType int int_orderMixin.


Section Integer.

Import GRing.
Import Num.Theory.

Lemma ordchar0_int : ordchar 0 (@predT int) = true.
Proof. by apply/ordchar0P; exists 0%R. Qed.

Lemma ordchar1_int : ordchar 1 (@predT int) = [set (true, true)].
Proof.
apply/setP => [] [[|] [|]]; rewrite ![in RHS]inE ?eqE /= ?eqE /= ?/eqb /=.
- apply/(mem_ordcharP (n := 0)) => /=.
  exists 0%R; split => //; apply/ordchar0P => /=.
  + by exists (- 1)%R.
  + by exists 1%R.
- apply/negP => /(mem_ordcharP (n := 0)) /= [i [_]].
  move=> _ /ordchar0P/= H; apply: H; exists (i + 1)%R.
  apply/upP; split => //=.
  by rewrite ltRealDomE ltz_addr1.
- apply/negP => /(mem_ordcharP (n := 0)) /= [i [_]].
  move=> /ordchar0P/= H _; apply: H; exists (i - 1)%R.
  apply/downP; split => //=.
  by rewrite ltRealDomE ltr_subl_addl addrC ltz_addr1.
- apply/negP => /(mem_ordcharP (n := 0)) /= [i [_]].
  move=> /ordchar0P/= H _; apply: H; exists (i - 1)%R.
  apply/downP; split => //=.
  by rewrite ltRealDomE ltr_subl_addl addrC ltz_addr1.
Qed.

Lemma isom_up_int (n : int) :
  is_isom (@predT nat) (up predT n) (fun i => (Posz i.+1) + n)%R.
Proof.
split => /=.
- by apply in2W => i j /addIr [].
- apply funext => z; rewrite !inE /=; apply/impredP/idP => /= [[i _ <-]|].
  + rewrite ltRealDomE -subr_gt0.
    by rewrite -addrA subrr addr0 ltz_nat.
  + move=> ltnz; exists (absz (z - (n+1))%R) => //.
    rewrite -addn1 PoszD -addrA [(1+n)%R]addrC gez0_abs.
      by rewrite -addrA [(- _ + _)%R]addrC subrr addr0.
    by rewrite subr_ge0 lez_addr1.
- move=> i j _ _ ltij.
  by rewrite ltRealDomE; apply ltr_le_add.
Qed.

End Integer.


Section Classification.

Variables (u : unit) (Ord : orderType u).
Implicit Type (x t : Ord) (P : pred Ord) (ch : ordchar_type 1).

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
Definition classif1 := map (fun pr : ordPred => ordchar 1 pr) classif1_order.
Definition classif1E := (ordchar_pred0 [orderType of nat], ordchar1_pred1 0%N,
                ordchar1_down2, ordchar1_down3, ordchar1_nat, ordchar1_nat_dual, ordchar1_int).

(* There are no duplicate in the classification *)
Proposition classif_uniq : uniq classif1.
Proof.
rewrite /classif1 /classif1_order /= !classif1E /=.
by rewrite !inE !eq_finset_enum enumftE /= /prod_enum enum_bool /= !inE.
Qed.

Theorem is_ordchar1E ch : (is_ordchar1 ch) = (ch \in classif1).
Proof.
apply/idP/idP.
- (* Expand the definitions and the classification *)
  rewrite /classif1 /classif1_order /= !classif1E /=.
  (* Expand computationally equality of ordchar 1 *)
  rewrite !inE !eq_finset_enum enumftE /= /prod_enum enum_bool /= !inE.
  (* case analysis *)
  by repeat case: (boolP (_ \in _)) => _; rewrite ?inE //=.
- rewrite !inE.
  by repeat move/orP => []; try (move/eqP->; exact: is_ordchar1P).
Qed.

(* All ordcharacters are in the classification *)
Corollary classifP P : ordchar 1 P \in classif1.
Proof. rewrite -is_ordchar1E; exact: is_ordchar1P. Qed.

End Classification.


Section Ordchar2.

Lemma down_predT0 : down predT 0%N = pred0.
Proof. by apply predext => x; rewrite !inE. Qed.
Lemma down_predT1 : down predT 1%N = pred1 0%N.
Proof. by apply predext => x; rewrite !inE ltEnat ltnS leqn0. Qed.


Definition chcl := nth set0 classif1.
Notation chcl0  := (chcl 0).
Notation chcl1  := (chcl 1).
Notation chcl2  := (chcl 2).
Notation chcl3  := (chcl 3).
Notation chclN  := (chcl 4).
Notation chclNd := (chcl 5).
Notation chclZ  := (chcl 6).

Variables (u : unit) (Ord : orderType u).
Implicit Type (x t : Ord) (P : pred Ord).

Lemma chcl0E : chcl0 = set0.
Proof. by rewrite /chcl /= ordchar_pred0. Qed.

Lemma ordchar2p_pred1 n x : ordchar n.+2 (pred1 x) = [set (set0, set0)].
Proof.
apply/setP => /= [[chu chd]]; rewrite [RHS]inE.
apply/(mem_ordcharP (n := n.+1))/eqP => [[x0 []] | [-> ->]].
- rewrite inE => /eqP ->{x0}.
  by rewrite up_pred1 down_pred1 ordchar_pred0 => <- <-.
- exists x; rewrite !inE.
  by split; rewrite // ?up_pred1 ?down_pred1 ordchar_pred0.
Qed.

Local Definition simpl_ordchar := (down_predT0, down_predT1,
                   classif1E, ordchar1_pred1, ordchar1_up_nat, ordchar1_down3plus).

Lemma ordchar2_nat :
  ordchar 2 (@predT nat) =
  [set (chcl0, chclN); (chcl1, chclN); (chcl2, chclN); (chcl3, chclN)].
Proof.
rewrite /chcl /= !classif1E.
apply/setP => [[chu chd]]; rewrite ![in RHS]inE -!orbA.
apply/(mem_ordcharP (n := 1))/idP=> /= [[x0 [_ <- <-]] {chu chd}|].
- by case: x0 => [|[|[|n]]]; rewrite ?simpl_ordchar ?eqxx ?orbT.
- move=> /or4P[]/eqP[-> ->]{chu chd}.
  + by exists 0%N; split => //; rewrite !simpl_ordchar.
  + by exists 1%N; split => //; rewrite !simpl_ordchar.
  + by exists 2%N; split => //; rewrite !simpl_ordchar.
  + by exists 3%N; split => //; rewrite !simpl_ordchar.
Qed.

End Ordchar2.
