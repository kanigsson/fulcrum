package Fulcrum with SPARK_Mode is
   --  This SPARK program solves the below problem:
   --
   --  Given a sequence of integers, returns the index i that minimizes
   --  |sum(seq[..i]) - sum(seq[i..])|. Does this in O(n) time and O(n)
   --  memory.
   --
   --  In fact, we give here an O(n) time and O(1) space solution. The SPARK
   --  solution is unique in that it uses bounded integers and proves absence
   --  of overflow.

   --  As mentioned, other solutions of the Fulcrum problem use unbounded
   --  integers. But SPARK doesn't have unbounded integers, and it adds a nice
   --  twist to the challenge to prove absence of overflow with bounded
   --  integers anyway.

   type Opt_Kind is (O_None, O_Some);
   type Opt_Nat (Kind : Opt_Kind) is record
      case Kind is
         when O_None => null;
         when O_Some =>
            Value : Natural;
      end case;
   end record;

   type Seq is array (Natural range <>) of Natural;
   --  [Seq] is the type of arrays that can be summed.

   function Overflows (A, B : Natural) return Boolean
   is (Natural'Last - A < B);

   function Safe_Add (A, B : Natural) return Opt_Nat
   is (if Overflows (A, B) then (Kind => O_None) else
         (O_Some, A + B));

   function Safe_Add (A : Opt_Nat; B : Natural) return Opt_Nat
   is (if A.Kind = O_None then A
         else Safe_Add (A.Value, B));

   function Safe_Sum (S : Seq; A, B : Natural) return Opt_Nat
   is (if A = B then (O_Some, S (A)) else
          Safe_Add (Safe_Sum (S, A, B - 1), S (B)))
     with Pre => A in S'Range and B in S'Range and A <= B,
     Subprogram_Variant => (Decreases => B);

   procedure Lemma_Safe_Sum_Left_Incr (S : Seq; A, B : Natural)
     with Pre                => A in S'Range and then B in S'Range and then A < B and then Safe_Sum (S, A, B).Kind = O_Some,
          Post               => Safe_Sum (S, A + 1, B).Kind = O_Some and then Safe_Sum (S, A + 1, B).Value <= Safe_Sum (S, A, B).Value,
          Annotate           => (GNATprove, Automatic_Instantiation),
          Subprogram_Variant => (Decreases => B),
          Ghost;

   function Sum (S : Seq; A, B : Natural) return Natural
   is (if A = B then S (A) else Sum (S, A, B - 1) + S (B))
     with Pre                =>
       A in S'Range and then B in S'Range and then A <= B
       and then Safe_Sum (S, A , B).Kind = O_Some,
          Post               => Sum'Result = Safe_Sum (S, A, B).Value,
          Subprogram_Variant => (Decreases => B);

   procedure Lemma_Left_Incr (S : Seq; A, B : Natural)
     with Pre  => A in S'Range and then B in S'Range and then A < B and then Safe_Sum (S, A, B).Kind = O_Some,
     Post => Sum (S, A, B) = Sum (S, A + 1, B) + S(A),
     Subprogram_Variant => (Decreases => B),
     Annotate => (GNATprove, Automatic_Instantiation),
     Ghost;

   function Diff_Sum (S : Seq; I : Natural) return Natural
   is (if I = S'Last then Sum (S, S'First, S'Last) else
          abs (Sum (S, S'First, I) - Sum (S, I + 1, S'Last)))
     with Pre => I in S'Range and then Safe_Sum (S, S'First, S'Las;
  --
  --   function ">=" (A, B : Opt_Nat) return Boolean
  --   is (A.Value >= B.Value)
  --     with Pre => A.Kind = O_Some and B.Kind = O_Some;
  --
  --  --  Now finally the [Find_Fulcrum] function. It simply states that no
  --  --  difference between the two sums is smaller than the one for the result.
  --  --  We use the arrays of partial sums to express that.
  --  function Find_Fulcrum (S : Seq) return Opt_Nat
  --  with Pre => S'Length > 1,
  --     Post =>
  --       (if (Find_Fulcrum'Result.Kind = O_None) then Sum (S, S'First, S'Last).Kind = O_None
  --          else
  --            (Find_Fulcrum'Result.Value in S'Range and then
  --               (for all I in S'Range =>
  --                      Diff_Sum (S, I)  >= Diff_Sum (S, Find_Fulcrum'Result.Value))));

end Fulcrum;
