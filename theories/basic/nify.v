From mathcomp Require Import ssreflect ssrbool ssrnat div eqtype.
Require Import Coq.omega.Omega.

Ltac nify :=
    repeat match goal with
          | [ H: is_true (leq _ _) |- _ ] => move /ltP in H
          | [ H: is_true (leq _ _) |- _ ] => move /leP in H
          | [ |- is_true (leq _ _) ] => apply /ltP
          | [ |- is_true (leq _ _) ] => apply /leP
          | [ H: ~ (is_true (leq _ _)) |- _ ] => move /negP/leP in H
          | [ |- ~ (is_true (leq _ _)) ] => apply /negP/leP
          | H: is_true (?a == ?b) |- _ => move /eqP in H
          | |- is_true (?a == ?b) => apply /eqP
          | H:context [ ?a + ?b ] |- _ => rewrite -plusE in H
          | |- context [ ?a + ?b ] => rewrite -plusE
          | H:context [ ?a - ?b ] |- _ => rewrite -minusE in H
          | |- context [ ?a - ?b ] => rewrite -minusE
          | H:context [ ?a * ?b ] |- _ => rewrite -multE in H
          | |- context [ ?a * ?b ] => rewrite -multE
          | H:context [ ?a / ?b ] |- _ => rewrite -multE in H
          | |- context [ ?a / ?b ] => rewrite -multE
          | H:context [ uphalf (double ?a) ] |- _ => rewrite uphalf_double in H
          | |- context [ uphalf (double ?a) ] => rewrite uphalf_double
          | H:context [ half (double ?a) ] |- _ => rewrite doubleK in H
          | |- context [ half (double ?a) ] => rewrite doubleK
          | H:context [ double ?a ] |- _ => rewrite -addnn in H
          | |- context [ double ?a ] => rewrite -addnn
    end.

Module nify_test.

Remark test00 a b c: (a + b + c).*2 = (a + a) + (b - b) + (b - b) + (b + b) + (c + c).
Proof. nify. omega. Qed.

Remark test01 a b c: (a + b + c).*2 * 5 = ((a + a) + (b - b) + (b - b) + (b + b) + (c + c))*5.
Proof. nify. omega. Qed.

Remark test02 a: (a.*2)./2.*2 = a + a.
Proof. nify. omega. Qed.

End nify_test.