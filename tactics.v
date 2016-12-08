Ltac decomp :=
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : exists _, _ |- _ ] => destruct H
         end.

Ltac inverts n :=
  match n with
  | S ?n' => match goal with
            | [ H : _ |- _ ] => try (inversion H; subst; inverts n')
            | _ => idtac
            end
  | _ => idtac
  end.

Ltac split_rec n :=
  match n with
  | S ?n' => match goal with
            |[ |- exists _, _ ] => eexists; split_rec n'
            |[ |- _ /\ _] => split; split_rec n'
            | _ => idtac
            end
  | 0 => idtac
  end.

Ltac subst_some :=
  repeat match goal with
         | [ G : ?x = Some ?y,
                 H : ?x = Some ?z |- _ ] => rewrite G in H
         | [ H : Some ?x = Some ?y |- _ ] => inversion H; subst; clear H
         end.