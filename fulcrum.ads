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
   --  Given that we sum the values of a sequence (array in our case), we need
   --  to bound the length of the sequence and the values that appear in the
   --  sequence.
   subtype Int is Integer range -1000 .. 1000;
   --  The type [Int] will be used for the elements of the array; we bound
   --  them arbitrarily at -1000 .. 1000. Given that the type is a subtype of
   --  Integer (32 or 64bit depending on platform), we could sum up a lot of
   --  those values without overflowing.
   subtype Nat is Integer range 1 .. 1000;
   --  This type is used for the index of the involved arrays. It means that
   --  arrays will be at most of size 1000. So if the array to be summed was
   --  of the maximum size 1000, and contained the maximum value of 1000 (or
   --  minimum value of -1000), we would get at most a sum of 1_000_000 (or
   --  -1_000_000), clearly within range of 32 (or 64) bit.
   --
   --  Those values (1000) are chosen arbitrarily and could be chosen larger.

   type Seq is array (Nat range <>) of Int;
   --  [Seq] is the type of arrays that can be summed. It uses [Nat] as index
   --  type and [Int] as value type.

   function Sum (S : Seq; A, B : Nat) return Integer
   is (if A = B then S (A) else Sum (S, A, B - 1) + S (B))
     with Pre => A in S'Range and B in S'Range and A <= B,
          Post => abs (Sum'Result) <= Int'Last * (B - A + 1),
     Subprogram_Variant => (Decreases => B);

   --  The sum function is defined by adding the last element to the recursive
   --  call. We prove that adding the first element instead would give the same
   --  result.
   procedure Lemma_Left_Incr (S : Seq; A, B : Nat)
     with Pre  => A in S'Range and B in S'Range and A < B,
     Post => Sum (S, A, B) = Sum (S, A + 1, B) + S(A),
     Subprogram_Variant => (Decreases => B),
     Annotate => (GNATprove, Automatic_Instantiation),
     Ghost;

   function Diff_Sum (S : Seq; I : Nat) return Integer
   is (if I = S'Last then abs (Sum (S, S'First, S'Last)) else
          abs (Sum (S, S'First, I) - Sum (S, I + 1, S'Last)))
     with Pre => I in S'Range;

  --  Now finally the [Find_Fulcrum] function. It simply states that no
  --  difference between the two sums is smaller than the one for the result.
  --  We use the arrays of partial sums to express that.
  function Find_Fulcrum (S : Seq) return Nat
  with Pre => S'Length > 0,
       Post =>
       (Find_Fulcrum'Result in S'Range and then
          (for all I in S'Range =>
               Diff_Sum (S, I)  >= Diff_Sum (S, Find_Fulcrum'Result)));

end Fulcrum;
