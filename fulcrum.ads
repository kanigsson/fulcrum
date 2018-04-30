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

   type Sum_Type is array (Nat range <>) of Integer;
   --  [Sum_Type] will be used for arrays that contain partial sums. We will
   --  see its use with the next function.

   --  A natural way to specify the sum of an array would be a recursive
   --  function. Such a function can be defined in SPARK, but SPARK proofs
   --  cannot use such a function for technical reasons. As a workaround, we
   --  now define two functions that return arrays of partial sums. The
   --  specification of Fulcrum nevertheless is quite nice.
   --  We could define more natural sum functions (e.g. Sum_Up_To (S, I) and
   --  Sum_From (S, I)), but we didn't find it necessary.

   --  [Sum_Acc] takes a sequence and returns a sequence of sums such that
   --  each cell contains the sum of values up to (and including) that cell.
   --  For example, Sum_Acc ( (1,2,3)) = (1,3,6)
   function Sum_Acc (S : Seq) return Sum_Type
      --  The function is marked "Ghost", which means it can only be used in
      --  specifications, not in code. This makes sure we don't use this
      --  costly function in the regular code.
     with Ghost,
     --  The Fulcrum problem doesn't really make sense with empty arrays, so
     --  we exclude this case for all functions in this example.
     Pre => S'Length > 0,
     Post =>
     --  the result has the same length and bounds as the input
     (Sum_Acc'Result'Length = S'Length and then
      Sum_Acc'Result'First = S'First and then
     --  (The absolute value of) Each partial sum can be bound by the number
     -- of elements it sums multiplied by the largest allowed value.
      (for all I in S'First .. S'Last =>
            abs (Sum_Acc'Result (I)) <= I * Int'Last) and then
      --  Now finally the conditions for the contents of the result. The first
      --  cell is the same as the first cell of the argument ...
      Sum_Acc'Result (S'First) = S (S'First) and then
      --  ..  and the other cells contain the current cell added to the
      --  previous cell.
      (for all I in S'First + 1 .. S'Last =>
            Sum_Acc'Result (I) = Sum_Acc'Result (I - 1) + S (I)));


   --  [Sum_Acc_Rev] takes a sequence and returns a sequence of sums such that
   --  each cell contains the sum of values up to (and excluding) that cell,
   --  starting from *the end* of the array.
   --  For example, Sum_Acc_Rev ((1,2,3)) = (5,3,0)
   --  The specification of [Sum_Acc_Rev] is of course very similar to
   --  [Sum_Acc], except that:
   --    - the last cell of the result always contains 0
   --    - the content of a cell is defined by the sum of the following cell
   --      of the result array and the *following* cell of the input array
   --    - to bound the sum values (to prove absence of overflow), we need to
   --      count summed values from the end of the array.
   function Sum_Acc_Rev (S : Seq) return Sum_Type
     with Ghost,
     Pre => S'Length > 0,
     Post =>
     (Sum_Acc_Rev'Result'Length = S'Length and then
      Sum_Acc_Rev'Result'First = S'First and then
      (for all I in S'First .. S'Last =>
         abs (Sum_Acc_Rev'Result (I)) <= (S'Last - I + 1) * Int'Last) and then
      Sum_Acc_Rev'Result (S'Last) = 0 and then
      (for all I in S'First .. S'Last - 1 =>
            Sum_Acc_Rev'Result (I) = Sum_Acc_Rev'Result (I + 1) + S (I + 1)));


  --  Now finally the [Find_Fulcrum] function. It simply states that no
  --  difference between the two sums is bigger than the one for the result.
  --  We use the arrays of partial sums to express that.
  function Find_Fulcrum (S : Seq) return Nat
  with Pre => S'Length > 0,
       Post =>
       (Find_Fulcrum'Result in S'Range and then
          (for all I in S'Range =>
               Sum_Acc (S) (I) - Sum_Acc_Rev (S) (I) <=
               Sum_Acc (S) (Find_Fulcrum'Result) - Sum_Acc_Rev (S) (Find_Fulcrum'Result)));

end Fulcrum;
