package body Fulcrum with SPARK_Mode is


   procedure Lemma_Left_Incr (S : Seq; A, B : Nat) is
   begin
      if A + 1 < B then
         Lemma_Left_Incr (S, A, B - 1);
      end if;
   end Lemma_Left_Incr;


  --  Finally the implementation of Find_Fulcrum. It uses two variables
  --  Left_Sum and Right_Sum which contain the current values for those
  --  partial sums, as well as the variable Min for the current minimal
  --  difference between the sum, and the variable Index for the
  --  corresponding index.
  function Find_Fulcrum (S : Seq) return Nat is
     --  We initialize those four local variables, basically setting the
     --  current best index at the first cell of the array.
     Index : Nat := S'First;
     --  The first partial sum from the left is just the first cell of the
     --  array.
     Left_Sum : Integer := S (S'First);
      --  The first partial sum from the right uses the Sum function. We need
      --  to exclude the first value so that Right_Sum corresponds to the sum
      --  excluding the first index.
      --  This is O(n) time, O(1) space.
      Right_Sum : Integer :=
        (if S'Length > 1 then Sum (S, S'First + 1, S'Last) else 0);
     --  The current best difference is just the first such difference.
     Min : Integer := abs (Left_Sum - Right_Sum);
  begin
     --  The code is now very straightforward. We iterate over the remainder
     --  of the array, adding the current value to the Left_Sum, and removing
     --  it from Right_Sum. We then compare their difference with the current
     --  best value Min, and update Min and Index if we found a new best
     --  value. This is clearly O(n) time. We don't do any calls or creation
     --  of new variables, so we stay at O(1) space.
     for I in S'First + 1 .. S'Last loop
        --  The loop invariants clearly express the intent of the four
        --  variables
        pragma Loop_Invariant
          --  We define what Left_Sum and Right_Sum are supposed to mean.
          (Left_Sum = Sum (S, S'First, I - 1) and then
           Right_Sum = Sum (S, I, S'Last) and then
          --  need to state that the Index variable is in range to be able to
          --  prove that the array accesses are within bounds
           Index in S'Range and then
          --  The link between Min and Index: Min contains the absolute
          --  difference between the partial sums at Index.
           Min = Diff_Sum (S, Index) and then
         --   and this is the best such difference up to now
          (for all K in S'First .. I - 1 => Diff_Sum (S, K) >= Min));
        Left_Sum := Left_Sum + S (I);
        Right_Sum := Right_Sum - S (I);
        if abs (Left_Sum - Right_Sum) < Min then
           Min := abs (Left_Sum - Right_Sum);
           Index := I;
        end if;
     end loop;
     return Index;
  end Find_Fulcrum;

end Fulcrum;
